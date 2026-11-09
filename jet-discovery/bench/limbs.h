/* Little-endian 64-bit limb helpers shared by the arithmetic sketches. */
#ifndef JD_LIMBS_H
#define JD_LIMBS_H
#include <stdint.h>
#include <stddef.h>
#include "frame.h"

typedef unsigned __int128 jd_u128;

/* Read n limbs of a big-endian frame word into little-endian x[0..n). */
static inline void jd_read_le(uint64_t* x, size_t n, frameItem* f) {
  for (size_t i = n; i-- > 0;) x[i] = simplicity_read64(f);
}
static inline void jd_write_le(frameItem* f, const uint64_t* x, size_t n) {
  for (size_t i = n; i-- > 0;) simplicity_write64(f, x[i]);
}

/* r[0..na+nb) = a * b, schoolbook. */
static inline void jd_mul(uint64_t* r, const uint64_t* a, size_t na, const uint64_t* b, size_t nb) {
  for (size_t i = 0; i < na + nb; ++i) r[i] = 0;
  for (size_t i = 0; i < na; ++i) {
    uint64_t carry = 0;
    for (size_t j = 0; j < nb; ++j) {
      jd_u128 t = (jd_u128)a[i] * b[j] + r[i + j] + carry;
      r[i + j] = (uint64_t)t;
      carry = (uint64_t)(t >> 64);
    }
    r[i + nb] = carry;
  }
}

/* Knuth algorithm D: q[0..n) = u / v and r[0..n) = u mod v for n-limb u, v.
 * v == 0 gives q = 0, r = u (the Simplicity div_mod convention). */
static inline void jd_divmod(uint64_t* q, uint64_t* r, const uint64_t* u, const uint64_t* v, size_t n) {
  size_t m = n, dn = n;
  while (dn > 0 && v[dn - 1] == 0) --dn;
  for (size_t i = 0; i < n; ++i) q[i] = 0;
  if (dn == 0) { for (size_t i = 0; i < n; ++i) r[i] = u[i]; return; }
  while (m > 0 && u[m - 1] == 0) --m;
  if (dn == 1) {
    jd_u128 rem = 0;
    for (size_t i = m; i-- > 0;) {
      jd_u128 cur = (rem << 64) | u[i];
      q[i] = (uint64_t)(cur / v[0]);
      rem = cur % v[0];
    }
    for (size_t i = 0; i < n; ++i) r[i] = 0;
    r[0] = (uint64_t)rem;
    return;
  }
  if (m < dn) { for (size_t i = 0; i < n; ++i) r[i] = u[i]; return; }
  uint64_t vn[16], un[17];
  int s = __builtin_clzll(v[dn - 1]);
  for (size_t i = dn - 1; i > 0; --i) vn[i] = s ? (v[i] << s) | (v[i - 1] >> (64 - s)) : v[i];
  vn[0] = v[0] << s;
  un[m] = s ? u[m - 1] >> (64 - s) : 0;
  for (size_t i = m - 1; i > 0; --i) un[i] = s ? (u[i] << s) | (u[i - 1] >> (64 - s)) : u[i];
  un[0] = u[0] << s;
  for (size_t j = m - dn + 1; j-- > 0;) {
    jd_u128 num = ((jd_u128)un[j + dn] << 64) | un[j + dn - 1];
    jd_u128 qhat = num / vn[dn - 1], rhat = num % vn[dn - 1];
    while (qhat >> 64 || qhat * vn[dn - 2] > ((rhat << 64) | un[j + dn - 2])) {
      --qhat; rhat += vn[dn - 1];
      if (rhat >> 64) break;
    }
    __int128 borrow = 0;
    uint64_t carry = 0;
    for (size_t i = 0; i < dn; ++i) {
      jd_u128 p = qhat * vn[i] + carry;
      carry = (uint64_t)(p >> 64);
      __int128 t = (__int128)un[i + j] - (uint64_t)p + borrow;
      un[i + j] = (uint64_t)t;
      borrow = t >> 64;
    }
    __int128 t = (__int128)un[j + dn] - carry + borrow;
    un[j + dn] = (uint64_t)t;
    q[j] = (uint64_t)qhat;
    if (t < 0) {
      --q[j];
      uint64_t c = 0;
      for (size_t i = 0; i < dn; ++i) {
        jd_u128 sum = (jd_u128)un[i + j] + vn[i] + c;
        un[i + j] = (uint64_t)sum;
        c = (uint64_t)(sum >> 64);
      }
      un[j + dn] += c;
    }
  }
  for (size_t i = 0; i < n; ++i) r[i] = 0;
  for (size_t i = 0; i < dn; ++i) r[i] = s ? (un[i] >> s) | (un[i + 1] << (64 - s)) : un[i];
}

/* 256-bit helpers on 4 little-endian limbs. */
static inline uint64_t jd_add4(uint64_t* r, const uint64_t* a, const uint64_t* b) {
  uint64_t c = 0;
  for (int i = 0; i < 4; ++i) { jd_u128 t = (jd_u128)a[i] + b[i] + c; r[i] = (uint64_t)t; c = (uint64_t)(t >> 64); }
  return c;
}
static inline uint64_t jd_sub4(uint64_t* r, const uint64_t* a, const uint64_t* b) {
  uint64_t borrow = 0;
  for (int i = 0; i < 4; ++i) {
    jd_u128 t = (jd_u128)a[i] - b[i] - borrow;
    r[i] = (uint64_t)t; borrow = (uint64_t)(t >> 64) & 1;
  }
  return borrow;
}
static inline void jd_copy4(uint64_t* r, const uint64_t* a) { for (int i = 0; i < 4; ++i) r[i] = a[i]; }
/* a < b */
static inline int jd_lt4(const uint64_t* a, const uint64_t* b) {
  for (int i = 4; i-- > 0;) if (a[i] != b[i]) return a[i] < b[i];
  return 0;
}
#endif
