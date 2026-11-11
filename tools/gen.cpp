// Hint generator / simulator for the verified search (untrusted helper).
//
// Usage: gen N side t EH ORDMIN ttbits out_prefix [simulate(0/1)]
//   side = B : find hints for "Black secures a margin >= t" (root is an OR node)
//   side = W : find hints for "White secures a margin >= t" (root is an AND node)
//   side = P : print a game in which both players play optimally, given that
//              the value of the initial position is t for Black
//   EH       : positions with at least EH empty squares get hints
//   ORDMIN   : the verified search orders moves "fastest first" when empties >= ORDMIN
// Output: out_prefix.hint (hint string), out_prefix.pos (horizon positions)
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
typedef uint64_t u64;

static int N = 6;
static u64 MASK = 0;
static u64 HM = ~0ULL;
static u64 nodes = 0;
static int ORDMIN = 8, EH = 22;

static inline int pc(u64 x) { return __builtin_popcountll(x); }
static const int DIRS[4] = {1, 8, 7, 9};

static inline u64 flips(u64 me, u64 opp, u64 mv) {
  u64 f = 0;
  for (int k = 0; k < 4; k++) {
    int s = DIRS[k];
    u64 o = (s == 8) ? opp : (opp & HM);
    u64 x = (mv << s) & o, g = 0;
    while (x) { g |= x; u64 nx = x << s; if (nx & me) { f |= g; break; } x = nx & o; }
    x = (mv >> s) & o; g = 0;
    while (x) { g |= x; u64 nx = x >> s; if (nx & me) { f |= g; break; } x = nx & o; }
  }
  return f;
}

static inline u64 mobility(u64 me, u64 opp) {
  u64 empty = MASK & ~(me | opp), mv = 0;
  for (int k = 0; k < 4; k++) {
    int s = DIRS[k];
    u64 o = (s == 8) ? opp : (opp & HM);
    u64 x = (me << s) & o;
    for (int i = 0; i < N - 3; i++) x |= (x << s) & o;
    mv |= x << s;
    x = (me >> s) & o;
    for (int i = 0; i < N - 3; i++) x |= (x >> s) & o;
    mv |= x >> s;
  }
  return mv & empty;
}

static inline int margin(u64 me, u64 opp) { return pc(me) - pc(opp); }

// ---------- oracle: alpha-beta with transposition table ----------
struct Entry { u64 me, opp; int8_t lo, hi; uint8_t best; uint8_t pad; };
static std::vector<Entry> TT;
static u64 TTMASK = 0;
static inline u64 hashpos(u64 me, u64 opp) {
  u64 h = me * 0x9E3779B97F4A7C15ULL;
  h ^= h >> 29;
  h += opp * 0xC2B2AE3D27D4EB4FULL;
  h ^= h >> 32;
  h *= 0x165667B19E3779F9ULL;
  h ^= h >> 29;
  return h;
}
static const int INF = 100;
static int search(u64 me, u64 opp, int alpha, int beta, bool passed);
static int search_nott(u64 me, u64 opp, int alpha, int beta, bool passed) {
  nodes++;
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (passed) return margin(me, opp);
    return -search_nott(opp, me, -beta, -alpha, true);
  }
  int best = -INF;
  while (mv) {
    u64 m = mv & -mv; mv ^= m;
    u64 f = flips(me, opp, m);
    int v = -search_nott(opp ^ f, me | m | f, -beta, -(alpha > best ? alpha : best), false);
    if (v > best) { best = v; if (best >= beta) return best; }
  }
  return best;
}
static int search(u64 me, u64 opp, int alpha, int beta, bool passed) {
  int empties = pc(MASK & ~(me | opp));
  if (empties < 7) return search_nott(me, opp, alpha, beta, passed);
  nodes++;
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (passed) return margin(me, opp);
    return -search(opp, me, -beta, -alpha, true);
  }
  u64 h = hashpos(me, opp) & TTMASK;
  Entry &e = TT[h];
  int ttbest = 255;
  if (e.me == me && e.opp == opp) {
    if (e.lo >= beta) return e.lo;
    if (e.hi <= alpha) return e.hi;
    if (e.lo == e.hi) return e.lo;
    if (e.lo > alpha) alpha = e.lo;
    if (e.hi < beta) beta = e.hi;
    ttbest = e.best;
  }
  struct M { u64 m, f; int key; };
  M ms[32]; int n = 0;
  u64 t = mv;
  while (t) {
    u64 m = t & -t; t ^= m;
    u64 f = flips(me, opp, m);
    u64 nme = opp ^ f, nopp = me | m | f;
    int sq = __builtin_ctzll(m);
    int key = pc(mobility(nme, nopp)) * 4;
    int x = sq & 7, y = sq >> 3;
    bool cx = (x == 0 || x == N - 1), cy = (y == 0 || y == N - 1);
    if (cx && cy) key -= 6;
    if (sq == ttbest) key -= 1000;
    ms[n++] = {m, f, key};
  }
  std::sort(ms, ms + n, [](const M &a, const M &b) { return a.key < b.key; });
  int best = -INF, a = alpha, bestsq = 255;
  for (int i = 0; i < n; i++) {
    u64 nme = opp ^ ms[i].f, nopp = me | ms[i].m | ms[i].f;
    int v;
    if (i == 0) v = -search(nme, nopp, -beta, -a, false);
    else {
      v = -search(nme, nopp, -a - 1, -a, false);
      if (v > a && v < beta) v = -search(nme, nopp, -beta, -v, false);
    }
    if (v > best) { best = v; bestsq = __builtin_ctzll(ms[i].m); if (v > a) a = v; if (best >= beta) break; }
  }
  Entry &e2 = TT[h];
  if (!(e2.me == me && e2.opp == opp)) { e2.me = me; e2.opp = opp; e2.lo = -INF; e2.hi = INF; e2.best = 255; }
  if (best <= alpha) { if (best < e2.hi) e2.hi = best; }
  else if (best >= beta) { if (best > e2.lo) e2.lo = best; e2.best = bestsq; }
  else { e2.lo = e2.hi = best; e2.best = bestsq; }
  return best;
}
// value(me to move) >= t ?
static bool wld_ge(u64 me, u64 opp, int t) { return search(me, opp, t - 1, t, false) >= t; }

// ---------- simulation of the verified search (no table) ----------
struct Cand { u64 m, f; int key; int sq; };
static int orderMoves(u64 me, u64 opp, u64 mv, Cand *out) {
  int n = 0;
  while (mv) {
    int sq = 63 - __builtin_clzll(mv); u64 m = 1ULL << sq; mv &= ~m;
    u64 f = flips(me, opp, m);
    int key = pc(mobility(opp ^ f, me | m | f));
    int p = 0; while (p < n && !(key <= out[p].key)) p++;
    for (int q = n; q > p; q--) out[q] = out[q - 1];
    out[p] = {m, f, key, sq}; n++;
  }
  return n;
}
static u64 simnodes = 0;
static bool secOpS(int t, u64 me, u64 opp);
static bool secMeS(int t, u64 me, u64 opp) {
  simnodes++;
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (!mobility(opp, me)) return t <= margin(me, opp);
    return secOpS(t, opp, me);
  }
  int e = pc(MASK & ~(me | opp));
  if (e >= ORDMIN) {
    Cand cs[32]; int n = orderMoves(me, opp, mv, cs);
    for (int i = 0; i < n; i++) if (secOpS(t, opp ^ cs[i].f, me | cs[i].m | cs[i].f)) return true;
    return false;
  }
  while (mv) {
    int sq = 63 - __builtin_clzll(mv); u64 m = 1ULL << sq; mv ^= m;
    u64 f = flips(me, opp, m);
    if (secOpS(t, opp ^ f, me | m | f)) return true;
  }
  return false;
}
static bool secOpS(int t, u64 me, u64 opp) {
  simnodes++;
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (!mobility(opp, me)) return t <= margin(opp, me);
    return secMeS(t, opp, me);
  }
  int e = pc(MASK & ~(me | opp));
  if (e >= ORDMIN) {
    Cand cs[32]; int n = orderMoves(me, opp, mv, cs);
    for (int i = 0; i < n; i++) if (!secMeS(t, opp ^ cs[i].f, me | cs[i].m | cs[i].f)) return false;
    return true;
  }
  while (mv) {
    int sq = 63 - __builtin_clzll(mv); u64 m = 1ULL << sq; mv ^= m;
    u64 f = flips(me, opp, m);
    if (!secMeS(t, opp ^ f, me | m | f)) return false;
  }
  return true;
}

// ---------- hint generation ----------
static FILE *fpos = nullptr;
static bool SIMULATE = false;
static u64 horizonCount = 0, zoneNodes = 0, simTotal = 0;
static std::string genOp(int t, u64 me, u64 opp);
static char enc(int sq) { return (char)(48 + sq); }

static void horizon(char kind, int t, u64 me, u64 opp) {
  horizonCount++;
  if (fpos) fprintf(fpos, "%c %d %llx %llx\n", kind, t, (unsigned long long)me, (unsigned long long)opp);
  if (SIMULATE) {
    u64 before = simnodes;
    bool r = (kind == 'M') ? secMeS(t, me, opp) : secOpS(t, me, opp);
    if (!r) { fprintf(stderr, "simulation failed at horizon!\n"); exit(1); }
    simTotal += simnodes - before;
  }
}

// the mover can secure >= t (expected to be true)
static std::string genMe(int t, u64 me, u64 opp) {
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (!mobility(opp, me)) { zoneNodes++; return ""; }
    zoneNodes++;
    return genOp(t, opp, me);   // pass: same hint is handed on
  }
  int e = pc(MASK & ~(me | opp));
  if (e < EH) { horizon('M', t, me, opp); return ""; }
  zoneNodes++;
  Cand cs[32]; int n = orderMoves(me, opp, mv, cs);
  for (int i = 0; i < n; i++) {
    u64 nme = opp ^ cs[i].f, nopp = me | cs[i].m | cs[i].f;
    // after the move the mover is the non-mover; needs value(child) <= -t
    if (!wld_ge(nme, nopp, 1 - t)) {
      std::string sub = genOp(t, nme, nopp);
      return std::string("(") + enc(cs[i].sq) + sub + ")";
    }
  }
  fprintf(stderr, "no good move found at an OR node (should not happen)\n");
  exit(1);
}
// the non-mover can secure >= t (expected to be true)
static std::string genOp(int t, u64 me, u64 opp) {
  u64 mv = mobility(me, opp);
  if (!mv) {
    if (!mobility(opp, me)) { zoneNodes++; return ""; }
    zoneNodes++;
    return genMe(t, opp, me);
  }
  int e = pc(MASK & ~(me | opp));
  if (e < EH) { horizon('O', t, me, opp); return ""; }
  zoneNodes++;
  Cand cs[32]; int n = orderMoves(me, opp, mv, cs);
  std::string s = "(";
  for (int i = 0; i < n; i++) {
    u64 nme = opp ^ cs[i].f, nopp = me | cs[i].m | cs[i].f;
    s += enc(cs[i].sq);
    s += genMe(t, nme, nopp);
  }
  s += ")";
  return s;
}

// ---------- an optimal line ----------
// Print a game in which every move keeps the value v (for the player to move).
static void optimalLine(int v, u64 me, u64 opp, bool blackToMove) {
  for (;;) {
    u64 mv = mobility(me, opp);
    if (!mv) {
      if (!mobility(opp, me)) break;
      printf("pass ");
      std::swap(me, opp); v = -v; blackToMove = !blackToMove;
      continue;
    }
    Cand cs[32]; int n = orderMoves(me, opp, mv, cs);
    bool found = false;
    for (int i = 0; i < n; i++) {
      u64 nme = opp ^ cs[i].f, nopp = me | cs[i].m | cs[i].f;
      if (!wld_ge(nme, nopp, 1 - v)) {
        printf("(%d, %d) ", cs[i].sq & 7, cs[i].sq >> 3);
        fflush(stdout);
        me = nme; opp = nopp; v = -v; blackToMove = !blackToMove; found = true;
        break;
      }
    }
    if (!found) { fprintf(stderr, "no optimal move found (wrong value?)\n"); exit(1); }
  }
  int b = blackToMove ? pc(me) : pc(opp), w = blackToMove ? pc(opp) : pc(me);
  printf("\nfinal: black %d, white %d\n", b, w);
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: gen N side t EH ORDMIN ttbits out_prefix [simulate]\n"); return 1; }
  N = atoi(argv[1]);
  char side = argv[2][0];
  int t = atoi(argv[3]);
  EH = atoi(argv[4]);
  ORDMIN = atoi(argv[5]);
  int ttbits = atoi(argv[6]);
  std::string prefix = argv[7];
  SIMULATE = argc > 8 && atoi(argv[8]) != 0;
  for (int y = 0; y < N; y++) for (int x = 0; x < N; x++) MASK |= 1ULL << (8 * y + x);
  if (N == 8) HM = 0x7E7E7E7E7E7E7E7EULL;
  TT.assign(1ULL << ttbits, Entry{0, 0, -INF, INF, 255, 0});
  TTMASK = (1ULL << ttbits) - 1;
  int h = N / 2;
  u64 white = (1ULL << (8 * (h - 1) + (h - 1))) | (1ULL << (8 * h + h));
  u64 black = (1ULL << (8 * (h - 1) + h)) | (1ULL << (8 * h + (h - 1)));
  fpos = fopen((prefix + ".pos").c_str(), "w");
  auto t0 = std::chrono::steady_clock::now();
  if (side == 'P') { optimalLine(t, black, white, true); return 0; }
  std::string hint = (side == 'B') ? genMe(t, black, white) : genOp(t, black, white);
  double dt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  fclose(fpos);
  FILE *fh = fopen((prefix + ".hint").c_str(), "w");
  fputs(hint.c_str(), fh);
  fclose(fh);
  printf("N=%d side=%c t=%d EH=%d ORDMIN=%d: hint length=%zu zone nodes=%llu horizon positions=%llu oracle nodes=%llu time=%.1fs\n",
         N, side, t, EH, ORDMIN, hint.size(), (unsigned long long)zoneNodes, (unsigned long long)horizonCount,
         (unsigned long long)nodes, dt);
  if (SIMULATE) printf("simulated verified-search nodes below the horizon: %llu (total %llu)\n",
                       (unsigned long long)simTotal, (unsigned long long)(simTotal + zoneNodes));
  return 0;
}
