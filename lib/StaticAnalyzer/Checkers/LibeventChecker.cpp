//===-- LibeventChecker.cpp -----------------------------------------*- C++ -*--//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
// TODO's:
// - support static event initialization
// - support Added/Removed states (event_del()/event_add())
//
// FIXME's:
// - destroy == free
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {
typedef SmallVector<SymbolRef, 2> SymbolVector;

struct EventState {
private:
  enum Kind { Null, Created, Destroyed } K;
  EventState(Kind InK) : K(InK) { }

public:
  bool isNull() const { return K == Null; }
  bool isCreated() const { return K == Created; }
  bool isDestroyed() const { return K == Destroyed; }

  static EventState getNull() { return EventState(Null); }
  static EventState getCreated() { return EventState(Created); }
  static EventState getDestroyed() { return EventState(Destroyed); }

  bool operator==(const EventState &X) const {
    return K == X.K;
  }
  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddInteger(K);
  }
};

class LibeventChecker : public Checker<check::PostCall,
                                       check::PreCall,
                                       check::DeadSymbols,
                                       check::PointerEscape> {

  mutable IdentifierInfo *IIevent_new, *IIevent_free;

  std::unique_ptr<BugType> UnitializedBugType;
  std::unique_ptr<BugType> DoubleDestroyBugType;
  std::unique_ptr<BugType> LeakBugType;

  void initIdentifierInfo(ASTContext &Ctx) const;

  void reportUnitialized(SymbolRef EventDescSym,
                         const CallEvent &Call,
                         CheckerContext &C) const;
  void reportDoubleDestroy(SymbolRef EventDescSym,
                           const CallEvent &Call,
                           CheckerContext &C) const;

  void reportLeaks(ArrayRef<SymbolRef> LeakedEvents, CheckerContext &C,
                   ExplodedNode *ErrNode) const;

  bool guaranteedNotToDestroyEvent(const CallEvent &Call) const;

public:
  LibeventChecker();

  /// Process event_new().
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  /// Process event_free().
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;

  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;

  /// Stop tracking addresses which escape.
  ProgramStateRef checkPointerEscape(ProgramStateRef State,
                                    const InvalidatedSymbols &Escaped,
                                    const CallEvent *Call,
                                    PointerEscapeKind Kind) const;
};

} // end anonymous namespace

/// The state of the checker is a map from tracked events to their
/// state. Let's store it in the ProgramState.
REGISTER_MAP_WITH_PROGRAMSTATE(EventMap, SymbolRef, EventState)

namespace {
class StopTrackingCallback : public SymbolVisitor {
  ProgramStateRef state;
public:
  StopTrackingCallback(ProgramStateRef st) : state(st) {}
  ProgramStateRef getState() const { return state; }

  bool VisitSymbol(SymbolRef sym) override {
    state = state->remove<EventMap>(sym);
    return true;
  }
};
} // end anonymous namespace

LibeventChecker::LibeventChecker()
    : IIevent_new(nullptr), IIevent_free(nullptr) {
  // Initialize the bug types.
  UnitializedBugType.reset(
      new BugType(this, "Unitialized event", "Libevent API Error"));

  DoubleDestroyBugType.reset(
      new BugType(this, "Double event_free", "Libevent API Error"));

  LeakBugType.reset(
      new BugType(this, "Resource Leak", "Libevent API Error"));
  // Sinks are higher importance bugs as well as calls to assert() or exit(0).
  LeakBugType->setSuppressOnSink(true);
}

void LibeventChecker::checkPostCall(const CallEvent &Call,
                                    CheckerContext &C) const {
  initIdentifierInfo(C.getASTContext());

  if (!Call.isGlobalCFunction())
    return;

  if (Call.getCalleeIdentifier() != IIevent_new)
    return;

  // Get the symbolic value corresponding to the event handle.
  SymbolRef EventDesc = Call.getReturnValue().getAsSymbol();
  if (!EventDesc)
    return;

  // Generate the next transition (an edge in the exploded graph).
  ProgramStateRef State = C.getState();
  State = State->set<EventMap>(EventDesc, EventState::getCreated());
  C.addTransition(State);
}

void LibeventChecker::checkPreCall(const CallEvent &Call,
                                   CheckerContext &C) const {
  initIdentifierInfo(C.getASTContext());

  if (!Call.isGlobalCFunction())
    return;

  if (Call.getCalleeIdentifier() != IIevent_free)
    return;

  if (Call.getNumArgs() != 1)
    return;

  // Get the symbolic value corresponding to the event.
  SymbolRef EventDesc = Call.getArgSVal(0).getAsSymbol();
  if (!EventDesc) {
    reportUnitialized(EventDesc, Call, C);
    return;
  }

  ProgramStateRef State = C.getState();
  const EventState *ES = State->get<EventMap>(EventDesc);
  if (ES && ES->isNull()) {
    reportUnitialized(EventDesc, Call, C);
    return;
  }
  // Check if the event has already been destroyed.
  if (ES && ES->isDestroyed()) {
    reportDoubleDestroy(EventDesc, Call, C);
    return;
  }

  // Generate the next transition, in which the event is destoyed.
  State = State->set<EventMap>(EventDesc, EventState::getDestroyed());
  C.addTransition(State);
}

static bool isLeaked(SymbolRef Sym, const EventState &ES,
                     bool IsSymDead, ProgramStateRef State) {
  if (IsSymDead && ES.isCreated()) {
    // If a symbol is NULL, assume that event_new() failed on this path.
    // A symbol should only be considered leaked if it is non-null.
    ConstraintManager &CMgr = State->getConstraintManager();
    ConditionTruthVal OpenFailed = CMgr.isNull(State, Sym);
    return !OpenFailed.isConstrainedTrue();
  }
  return false;
}

void LibeventChecker::checkDeadSymbols(SymbolReaper &SymReaper,
                                       CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  SymbolVector LeakedEvents;
  EventMapTy TrackedEvents = State->get<EventMap>();
  for (EventMapTy::iterator I = TrackedEvents.begin(),
                             E = TrackedEvents.end(); I != E; ++I) {
    SymbolRef Sym = I->first;
    bool IsSymDead = SymReaper.isDead(Sym);

    // Collect leaked symbols.
    if (isLeaked(Sym, I->second, IsSymDead, State))
      LeakedEvents.push_back(Sym);

    // Remove the dead symbol from the events map.
    if (IsSymDead)
      State = State->remove<EventMap>(Sym);
  }

  ExplodedNode *N = C.addTransition(State);
  reportLeaks(LeakedEvents, C, N);
}

void LibeventChecker::reportUnitialized(SymbolRef EventDescSym,
                                        const CallEvent &Call,
                                        CheckerContext &C) const {
  // We reached a bug, stop exploring the path here by generating a sink.
  ExplodedNode *ErrNode = C.generateSink();
  // If we've already reached this node on another path, return.
  if (!ErrNode)
    return;

  // Generate the report.
  BugReport *R = new BugReport(*UnitializedBugType,
      "Unitialized event", ErrNode);
  R->addRange(Call.getSourceRange());
  R->markInteresting(EventDescSym);
  C.emitReport(R);
}

void LibeventChecker::reportDoubleDestroy(SymbolRef EventDescSym,
                                          const CallEvent &Call,
                                          CheckerContext &C) const {
  // We reached a bug, stop exploring the path here by generating a sink.
  ExplodedNode *ErrNode = C.generateSink();
  // If we've already reached this node on another path, return.
  if (!ErrNode)
    return;

  // Generate the report.
  BugReport *R = new BugReport(*DoubleDestroyBugType,
      "Freeing a previously freed event", ErrNode);
  R->addRange(Call.getSourceRange());
  R->markInteresting(EventDescSym);
  C.emitReport(R);
}

void LibeventChecker::reportLeaks(ArrayRef<SymbolRef> LeakedEvents,
                                  CheckerContext &C,
                                  ExplodedNode *ErrNode) const {
  // Attach bug reports to the leak node.
  // TODO: Identify the leaked event.
  for (SymbolRef LeakedEvent : LeakedEvents) {
    BugReport *R = new BugReport(*LeakBugType,
        "Created event is never freed; potential resource leak", ErrNode);
    R->markInteresting(LeakedEvent);
    C.emitReport(R);
  }
}

bool LibeventChecker::guaranteedNotToDestroyEvent(const CallEvent &Call) const{
  // If it's not in a system header, assume it might destroy an event.
  if (!Call.isInSystemHeader())
    return false;

  // Handle cases where we know a buffer's /address/ can escape.
  if (Call.argumentsMayEscape())
    return false;

  // Note, even though event_free() destroy the event, we do not list it here
  // since the checker is modeling the call.

  return true;
}

// If the pointer we are tracking escaped, do not track the symbol as
// we cannot reason about it anymore.
ProgramStateRef
LibeventChecker::checkPointerEscape(ProgramStateRef State,
                                    const InvalidatedSymbols &Escaped,
                                    const CallEvent *Call,
                                    PointerEscapeKind Kind) const {
  // If we know that the call cannot destroy an event, there is nothing to do.
  if (Kind == PSK_DirectEscapeOnCall && guaranteedNotToDestroyEvent(*Call)) {
    return State;
  }

  for (InvalidatedSymbols::const_iterator I = Escaped.begin(),
                                          E = Escaped.end();
                                          I != E; ++I) {
    SymbolRef Sym = *I;

    // The symbol escaped. Optimistically, assume that the corresponding event
    // handle will be freed somewhere else.
    State = State->remove<EventMap>(Sym);
  }
  return State;
}

void LibeventChecker::initIdentifierInfo(ASTContext &Ctx) const {
  if (IIevent_new)
    return;
  IIevent_new = &Ctx.Idents.get("event_new");
  IIevent_free = &Ctx.Idents.get("event_free");
}

void ento::registerLibeventChecker(CheckerManager &mgr) {
  mgr.registerChecker<LibeventChecker>();
}
