// Top of the proof tree for 8x8 Othello (an untrusted helper).
//
// Input: empty50_tasklist_edax_knowledge.csv from
//   https://github.com/eukaryo/reversi-scripts  (H. Takizawa, "Othello is Solved")
// which lists 2587 positions with 50 empty squares (Black to move) together
// with the bound that was needed -- and, according to the paper, proved -- for
// each of them:  value >= 0,  value <= 0,  or value = 0.
//
// This program searches the first ten plies of the game and finds
//   * a strategy tree showing "Black secures a draw" whose leaves are table
//     positions with value >= 0, and
//   * a strategy tree showing "White secures a draw" whose leaves are table
//     positions with value <= 0
// (table positions are matched up to the eight symmetries of the board).
// It writes the two trees as hint strings for the verified search of
// Othello/Eight.lean, and the table as Lean data.
//
// Usage: top8 tasklist.csv out_prefix
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <unordered_map>
#include <algorithm>
typedef uint64_t u64;

static const u64 HM = 0x7E7E7E7E7E7E7E7EULL;
static const int DIRS[4] = {1, 8, 7, 9};
static inline int pc(u64 x) { return __builtin_popcountll(x); }

static u64 flips(u64 me, u64 opp, u64 mv) {
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
static u64 mobility(u64 me, u64 opp) {
  u64 empty = ~(me | opp), mv = 0;
  for (int k = 0; k < 4; k++) {
    int s = DIRS[k];
    u64 o = (s == 8) ? opp : (opp & HM);
    u64 x = (me << s) & o;
    for (int i = 0; i < 5; i++) x |= (x << s) & o;
    mv |= x << s;
    x = (me >> s) & o;
    for (int i = 0; i < 5; i++) x |= (x >> s) & o;
    mv |= x >> s;
  }
  return mv & empty;
}

// the eight symmetries of the board
static u64 sym(u64 b, int k) {
  u64 r = 0;
  for (int i = 0; i < 64; i++) if (b >> i & 1) {
    int x = i & 7, y = i >> 3;
    if (k & 1) std::swap(x, y);
    if (k & 2) x = 7 - x;
    if (k & 4) y = 7 - y;
    r |= 1ULL << (8 * y + x);
  }
  return r;
}

enum { LOWER = 1, UPPER = 2 };  // bit set: value >= 0 known / value <= 0 known
struct Key { u64 b, w; bool operator==(const Key &o) const { return b == o.b && w == o.w; } };
struct KeyHash { size_t operator()(const Key &k) const { return k.b * 0x9E3779B97F4A7C15ULL ^ (k.w + 0x165667B19E3779F9ULL) * 0xC2B2AE3D27D4EB4FULL; } };
static std::unordered_map<Key, int, KeyHash> table;      // all symmetric images
static std::unordered_map<Key, int, KeyHash> entryId;    // image -> index of the csv row
struct Row { u64 b, w; int kind; };
static std::vector<Row> rows;

// memo of the search: claim 0 = "Black secures >= 0", claim 1 = "White secures >= 0"
struct Node { u64 b, w; int turn, claim; bool operator==(const Node &o) const { return b == o.b && w == o.w && turn == o.turn && claim == o.claim; } };
struct NodeHash { size_t operator()(const Node &n) const { return KeyHash()(Key{n.b, n.w}) * 4 + n.turn * 2 + n.claim; } };
static std::unordered_map<Node, std::pair<bool, double>, NodeHash> memo;   // proved?, size of the smallest tree found
static std::vector<char> used;

// returns (proved, tree size)
static std::pair<bool, double> prove(int claim, u64 b, u64 w, int turn /*0 = Black*/) {
  Node nd{b, w, turn, claim};
  auto it = memo.find(nd);
  if (it != memo.end()) return it->second;
  std::pair<bool, double> res(false, 0);
  int empties = 64 - pc(b | w);
  u64 me = turn == 0 ? b : w, opp = turn == 0 ? w : b;
  u64 mv = mobility(me, opp);
  if (empties == 50) {
    // the frontier: only the table may be used here
    if (turn == 0) {
      auto t = table.find(Key{b, w});
      if (t != table.end() && (t->second & (claim == 0 ? LOWER : UPPER))) res = {true, 1};
    }
  } else if (!mv) {
    if (!mobility(opp, me)) {
      int d = pc(b) - pc(w);
      res = {claim == 0 ? d >= 0 : d <= 0, 1};
    } else {
      auto r = prove(claim, b, w, 1 - turn);
      res = {r.first, r.second + 1};
    }
  } else if (turn == claim) {
    // the claimant moves: one good move is enough; keep the smallest tree
    bool ok = false; double best = 1e300;
    for (u64 t = mv; t; t &= t - 1) {
      u64 m = t & -t, f = flips(me, opp, m);
      u64 nme = me | m | f, nopp = opp ^ f;
      auto r = turn == 0 ? prove(claim, nme, nopp, 1) : prove(claim, nopp, nme, 0);
      if (r.first && r.second < best) { ok = true; best = r.second; }
    }
    res = {ok, ok ? best + 1 : 0};
  } else {
    bool ok = true; double total = 1;
    for (u64 t = mv; t && ok; t &= t - 1) {
      u64 m = t & -t, f = flips(me, opp, m);
      u64 nme = me | m | f, nopp = opp ^ f;
      auto r = turn == 0 ? prove(claim, nme, nopp, 1) : prove(claim, nopp, nme, 0);
      if (!r.first) ok = false; else total += r.second;
    }
    res = {ok, ok ? total : 0};
  }
  memo[nd] = res;
  return res;
}

static long long treeNodes = 0, treeLeaves = 0;
static char enc(int sq) { return (char)(48 + sq); }

// write the strategy tree found by prove() as a hint string
static std::string emit(int claim, u64 b, u64 w, int turn) {
  treeNodes++;
  int empties = 64 - pc(b | w);
  u64 me = turn == 0 ? b : w, opp = turn == 0 ? w : b;
  u64 mv = mobility(me, opp);
  if (empties == 50) {
    treeLeaves++;
    auto e = entryId.find(Key{b, w});
    if (e != entryId.end()) used[e->second] |= (claim == 0 ? LOWER : UPPER);
    return "";
  }
  if (!mv) {
    if (!mobility(opp, me)) { treeLeaves++; return ""; }
    return emit(claim, b, w, 1 - turn);   // the hint is handed on over a pass
  }
  std::string s = "(";
  if (turn == claim) {
    double best = 1e300; u64 bm = 0;
    for (u64 t = mv; t; t &= t - 1) {
      u64 m = t & -t, f = flips(me, opp, m);
      u64 nme = me | m | f, nopp = opp ^ f;
      auto r = turn == 0 ? prove(claim, nme, nopp, 1) : prove(claim, nopp, nme, 0);
      if (r.first && r.second < best) { best = r.second; bm = m; }
    }
    u64 f = flips(me, opp, bm);
    u64 nme = me | bm | f, nopp = opp ^ f;
    s += enc(__builtin_ctzll(bm));
    s += turn == 0 ? emit(claim, nme, nopp, 1) : emit(claim, nopp, nme, 0);
  } else {
    for (u64 t = mv; t; t &= t - 1) {
      u64 m = t & -t, f = flips(me, opp, m);
      u64 nme = me | m | f, nopp = opp ^ f;
      s += enc(__builtin_ctzll(m));
      s += turn == 0 ? emit(claim, nme, nopp, 1) : emit(claim, nopp, nme, 0);
    }
  }
  s += ")";
  return s;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: top8 tasklist.csv out_prefix\n"); return 1; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror("tasklist"); return 1; }
  char line[512];
  int nl = 0, nu = 0, ne = 0;
  while (fgets(line, sizeof line, f)) {
    if (strlen(line) < 67 || (line[0] != '-' && line[0] != 'O' && line[0] != 'X')) continue;
    u64 b = 0, w = 0;
    for (int i = 0; i < 64; i++) {
      if (line[i] == 'X') b |= 1ULL << i;
      else if (line[i] == 'O') w |= 1ULL << i;
      else if (line[i] != '-') { fprintf(stderr, "bad board\n"); return 1; }
    }
    if (strncmp(line + 64, " X;,", 4) != 0) { fprintf(stderr, "unexpected side to move\n"); return 1; }
    int count, score, alpha, beta;
    if (sscanf(line + 68, "%d,%d,%d,%d", &count, &score, &alpha, &beta) != 4) { fprintf(stderr, "bad row\n"); return 1; }
    if (64 - pc(b | w) != 50) { fprintf(stderr, "not 50 empties\n"); return 1; }
    int kind;
    if (alpha < score && score < beta) {
      // full window: the exact value was computed; the paper's conclusion (a draw) says it is 0
      if (!(alpha == -64 && beta == 64 && score == 0)) { fprintf(stderr, "unexpected exact row\n"); return 1; }
      kind = LOWER | UPPER; ne++;
    } else if (beta <= score) {
      if (beta != 0) { fprintf(stderr, "unexpected lower-bound row\n"); return 1; }
      kind = LOWER; nl++;
    } else {
      if (alpha != 0) { fprintf(stderr, "unexpected upper-bound row\n"); return 1; }
      kind = UPPER; nu++;
    }
    int id = (int)rows.size();
    rows.push_back(Row{b, w, kind});
    for (int k = 0; k < 8; k++) {
      Key key{sym(b, k), sym(w, k)};
      table[key] |= kind;
      entryId[key] = id;
    }
  }
  fclose(f);
  used.assign(rows.size(), 0);
  printf("table: %zu rows (%d lower bounds, %d upper bounds, %d exact), %zu symmetric images\n",
         rows.size(), nl, nu, ne, table.size());

  u64 white = (1ULL << 27) | (1ULL << 36), black = (1ULL << 28) | (1ULL << 35);
  std::string prefix = argv[2];
  const char *names[2] = {"black", "white"};
  for (int claim = 0; claim < 2; claim++) {
    auto r = prove(claim, black, white, 0);
    printf("%s secures a draw: %s (smallest tree found: %.0f nodes; %zu positions examined)\n",
           names[claim], r.first ? "proved from the table" : "NOT proved", r.second, memo.size());
    if (!r.first) return 1;
    treeNodes = treeLeaves = 0;
    std::string h = emit(claim, black, white, 0);
    printf("  hint string: %zu characters, %lld nodes, %lld leaves\n", h.size(), treeNodes, treeLeaves);
    FILE *o = fopen((prefix + "_" + names[claim] + ".hint").c_str(), "w");
    fputs(h.c_str(), o);
    fclose(o);
  }
  int usedCount = 0, usedL = 0, usedU = 0;
  for (size_t i = 0; i < rows.size(); i++) { if (used[i]) usedCount++; if (used[i] & LOWER) usedL++; if (used[i] & UPPER) usedU++; }
  printf("table rows used by the two trees: %d of %zu (%d as lower bounds, %d as upper bounds)\n",
         usedCount, rows.size(), usedL, usedU);
  // the table as data: black bits, white bits, kind (1: value >= 0, 2: value <= 0, 3: value = 0)
  FILE *o = fopen((prefix + "_table.txt").c_str(), "w");
  for (auto &r : rows) fprintf(o, "%llu %llu %d\n", (unsigned long long)r.b, (unsigned long long)r.w, r.kind);
  fclose(o);
  return 0;
}
