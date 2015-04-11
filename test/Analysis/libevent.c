// RUN: %clang_cc1 -analyze -analyzer-checker=alpha.core.Libevent -I/usr/include -I/usr/lib/gcc/x86_64-linux-gnu/4.9/include %s

#include <event2/event.h>

void uninitialized(int fd1, int fd2)
{
  struct event *ev2;
  event_free(ev2); // expected-warning{{Unitialized event}}
}

void never_freed(int fd1, int fd2)
{
  struct event *ev1;
  ev1 = event_new(NULL, fd1, 0, NULL,NULL); // expected-warning{{Created event is never freed; potential resource leak}}
}

void double_free(int fd1, int fd2)
{
  struct event *ev2;
  ev2 = event_new(NULL, fd1, 0, NULL,NULL);
  event_free(ev2);
  event_free(ev2); // expected-warning{{Freeing a previously freed event}}
}

