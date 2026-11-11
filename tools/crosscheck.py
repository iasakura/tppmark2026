# simple array-based Othello to cross-check perft numbers and a game record
import sys
sys.setrecursionlimit(10000)
DIRS = [(-1,-1),(0,-1),(1,-1),(-1,0),(1,0),(-1,1),(0,1),(1,1)]
def initial(n):
    h = n // 2
    b = {}
    b[(h-1,h-1)] = 'W'; b[(h,h)] = 'W'
    b[(h,h-1)] = 'B'; b[(h-1,h)] = 'B'
    return b
def opp(c): return 'W' if c == 'B' else 'B'
def flips(n, b, c, s):
    res = []
    for dx, dy in DIRS:
        x, y = s[0]+dx, s[1]+dy
        run = []
        while 0 <= x < n and 0 <= y < n and b.get((x,y)) == opp(c):
            run.append((x,y)); x += dx; y += dy
        if run and 0 <= x < n and 0 <= y < n and b.get((x,y)) == c:
            res += run
    return res
def moves(n, b, c):
    return [(x,y) for y in range(n) for x in range(n) if (x,y) not in b and flips(n,b,c,(x,y))]
def play(n, b, c, s):
    nb = dict(b)
    for q in flips(n,b,c,s): nb[q] = c
    nb[s] = c
    return nb
def perft(n, d, b, c):
    if d == 0: return 1
    ms = moves(n, b, c)
    if not ms:
        if not moves(n, b, opp(c)): return 1
        return perft(n, d-1, b, opp(c))
    return sum(perft(n, d-1, play(n,b,c,s), opp(c)) for s in ms)
if __name__ == '__main__':
    print('perft 8:', [perft(8, d, initial(8), 'B') for d in range(1, 8)])
    print('perft 6:', [perft(6, d, initial(6), 'B') for d in range(1, 8)])
    print('perft 4:', [perft(4, d, initial(4), 'B') for d in range(1, 13)])
    line = "F5D6C3D3C4F4F6F3E6E7D7C5B6D8C6C7D2B5A5A6A7G5E3B4C8G6G4C2E8D1F7E2G3H4F1E1F2G1B1F8G8B3H3B2H5B7A3A4A1A2C1H2H1G2B8A8G7H8H7H6"
    print('line length', len(line)//2)
    b = initial(8); c = 'B'; ok = True; passes = 0
    for k in range(0, len(line), 2):
        s = (ord(line[k]) - ord('A'), int(line[k+1]) - 1)
        ms = moves(8, b, c)
        if not ms:
            c = opp(c); passes += 1
            ms = moves(8, b, c)
        if s not in ms:
            print('illegal move', line[k:k+2], 'at ply', k//2 + 1, 'for', c); ok = False; break
        b = play(8, b, c, s); c = opp(c)
    nb = sum(1 for v in b.values() if v == 'B'); nw = sum(1 for v in b.values() if v == 'W')
    print('ok', ok, 'passes', passes, 'black', nb, 'white', nw, 'moves left', len(moves(8,b,'B')), len(moves(8,b,'W')))
