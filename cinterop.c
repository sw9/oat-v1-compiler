#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

void ll_puts(int8_t *s) {
  puts((char *)s);
}

int8_t* ll_strcat(int8_t* s1, int8_t* s2) {
  int l1 = strlen((char*)s1);
  int l2 = strlen((char*)s2);
  char* buf = (char*)calloc(0, sizeof(char) * (l1 + l2 + 1));
  strncpy(buf, (char*)s1, l1);
  strncpy(buf + l1, (char*)s2, l2+1);
  return (int8_t*) buf;
}

int64_t ll_callback(int64_t (*fun)(int64_t, int64_t)) {
  int64_t x = 19L;
  return fun(x, x);
}

int8_t* ll_ltoa(int64_t i) {
  char* buf = (char*)calloc(0, sizeof(char) * 20);
  snprintf((char *)buf, 20, "%ld", (long)i);
  return (int8_t *)buf;
}


