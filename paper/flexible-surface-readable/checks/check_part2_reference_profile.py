"""Machine checks, Part II of the paper (Sections 4-6)."""
import sympy as sp, mpmath as mp, numpy as np
from scipy.integrate import solve_ivp, quad
from scipy.linalg import eigh_tridiagonal
ok = True
def rep(name, good, info=""):
    global ok
    ok &= bool(good)
    print(f"{'PASS' if good else 'FAIL'}  {name:66s} {info}")

X, r_, y, lam, j = sp.symbols('X r y lambda j', positive=True)

# ---------------- Lemma 4.3 (Liouville)
rX = sp.Function('r')(X); P = sp.Function('P')(X); psi = sp.Function('psi')(X)
rho = -(sp.diff(rX, X, 2) + sp.diff(P, X)/P*sp.diff(rX, X))/rX
V0 = sp.diff(sp.sqrt(P), X, 2)/sp.sqrt(P)
w = lam*P*sp.diff(rX, X)
u = psi/sp.sqrt(P)
ddr = lambda f: sp.diff(f, X)/sp.diff(rX, X)
Lj = ddr(w*ddr(u)) - j**2*ddr(w)/rX*u
rhs = -lam*sp.sqrt(P)/sp.diff(rX, X)*(-sp.diff(psi, X, 2) + (V0 - j**2*rho)*psi)
rep("Lemma 4.3: Liouville identity", sp.simplify(Lj - rhs) == 0)
rep("Lemma 4.3: w' = -lam P rho r / r_X", sp.simplify(ddr(w) + lam*P*rho*rX/sp.diff(rX, X)) == 0)
rep("travel angle: sqrt(-w'/(r w)) dr = sqrt(rho) dX  (squares)",
    sp.simplify(-ddr(w)/(rX*w)*sp.diff(rX, X)**2 - rho) == 0)

# ---------------- central oscillator
Ac = 1/mp.sqrt(2); ac = mp.sqrt(4*Ac - 2); cc = 3*Ac - 2; alc = (cc + 1)/2
dc = mp.mpf(3)/4*(3 - 2*mp.sqrt(2))
rep("central: E_{0,2}=0 and c_c - a_c^2 + A_c = 0", abs(2 + ac**2 - 4*Ac) < 1e-25 and abs(cc - ac**2 + Ac) < 1e-25)
mp.mp.dps = 40
worst = mp.inf
for jj in list(range(4, 20001, 2)) + [10**6 + 2*i for i in range(2000)] + [10**9 + 2*i for i in range(200)]:
    Phi = jj*Ac - ac**2/jj
    m = mp.nint((Phi - 1)/2)
    worst = min(worst, min(abs(jj*(2*mm + 1 - Phi)) for mm in (m - 1, m, m + 1)))
rep("Lemma 4.4: min |E_{m,j}| >= delta_c/2 (even j>=4, sampled to 1e9)", worst >= dc/2,
    f"min={mp.nstr(worst,6)}  delta_c/2={mp.nstr(dc/2,6)}")
mp.mp.dps = 25
psi1 = lambda x: mp.exp(-x*x/2)*mp.quad(lambda t: t**(alc - 1)*mp.exp(-t*t/2 + mp.sqrt(2)*x*t), [0, 1, 5, 20, 60])
errs = []
for x0 in (-3, -1, 0, 1.5, 3):
    d2 = mp.diff(psi1, x0, 2); errs.append(abs(d2 - (x0**2 + cc)*psi1(x0))/abs(psi1(x0)))
rep("Lemma 4.5: psi_1'' = (X^2 + c_c) psi_1", max(errs) < 1e-8, f"max rel err={mp.nstr(max(errs),3)}")
ups = lambda x: ac + mp.diff(psi1, x)/psi1(x)
e1 = [abs(ups(-x) - (x + ac + alc/x))*x**3 for x in (6, 9, 12)]
e2 = [abs(ups(x) - (x + ac + (alc - 1)/x))*x**3 for x in (6, 9, 12)]
rep("Lemma 4.5: asymptotics (sc6a), remainder * |X|^3 bounded", max(e1 + e2) < 2,
    f"left {[mp.nstr(v,3) for v in e1]} right {[mp.nstr(v,3) for v in e2]}")
rep("Lemma 4.5: upsilon > a_c", all(ups(x) > ac for x in (-8, -3, 0, 2, 7)))
T = mp.quad(lambda x: mp.sqrt(Ac - x*x), [-mp.sqrt(Ac), mp.sqrt(Ac)])
rep("central travel angle = pi/(2 sqrt 2)", abs(T - mp.pi/(2*mp.sqrt(2))) < 1e-15)

# ---------------- Morse model
def morse_levels(d, jj):
    A = (d**-0.5 + 2*d**-4.5)**2; B = d**-9.0
    al = (jj*np.sqrt(A) - 1)/2
    return A, B, [jj*jj*B - (al - m)**2 for m in range(int(np.floor(al)) + 1) if m < al]
def morse_fd(d, jj, n=6000):
    A, B, _ = morse_levels(d, jj)
    xs = np.linspace(-np.log(60*jj) / 1 - 2, 45.0, n); h = xs[1] - xs[0]
    V = jj*jj*(A*(np.exp(-2*xs) - np.exp(-xs)) + B)
    ev = eigh_tridiagonal(2/h**2 + V, -np.ones(n - 1)/h**2, select='i', select_range=(0, 3))[0]
    return ev
for d, jj in ((2, 8), (3, 12), (5, 20)):
    A, B, lev = morse_levels(d, jj); ev = morse_fd(d, jj)
    k = min(len(lev), 3)
    err = max(abs(ev[i] - lev[i]) for i in range(k))
    rep(f"Morse spectrum (fs1) vs finite differences, d={d}, j={jj}", err < 2e-3, f"levels {np.round(lev[:k],5)} err={err:.1e}")
mp.mp.dps = 60
for d in (2, 3, 5, 7, 10**3 + 1, 10**6 + 3):
    sA = mp.mpf(d)**-0.5 + 2*mp.mpf(d)**-4.5; B = mp.mpf(d)**-9
    worst = mp.inf
    for jj in list(range(2, 4001)) + [10**5 + i for i in range(300)]:
        al = (jj*sA - 1)/2
        m0 = mp.nint(al - jj*mp.sqrt(B))
        for m in (m0 - 1, m0, m0 + 1):
            if 0 <= m < al: worst = min(worst, abs(jj*jj*B - (al - m)**2))
        worst = min(worst, jj*jj*B)
    rep(f"Lemma 4.7: gap at zero >= 1/(8 d^9), d={d}", worst >= 1/(8*mp.mpf(d)**9),
        f"min/(1/8d^5)={mp.nstr(worst*8*mp.mpf(d)**5,5)}")
for d in (2, 3, 5, 7):
    A = (d**-0.5 + 2*d**-4.5)**2; B = d**-9.0
    tm, tp = np.roots([A, -A, B]).min(), np.roots([A, -A, B]).max()
    Tn = quad(lambda t: np.sqrt(max(A*(t - tm)*(tp - t), 0))/t, tm, tp, limit=400)[0]
    ks = np.arange(1, 400001); sd = np.min(np.abs(np.sin(ks*np.pi/(2*np.sqrt(d))))*ks*3*np.sqrt(d))
    rep(f"Lemma 4.7: T = pi/(2 sqrt d) and |sin kT| >= 1/(3k sqrt d), d={d}",
        abs(Tn - np.pi/(2*np.sqrt(d))) < 1e-7 and sd >= 1, f"T err={abs(Tn-np.pi/(2*np.sqrt(d))):.1e}, min ratio={sd:.3f}")
al_, om, Bq, jq = sp.symbols('alpha omega B j', real=True)
f = sp.Function('f')(X)
Dal = lambda g, a: sp.diff(g, X) + (a - om*sp.exp(-X))*g
Dst = lambda g, a: -sp.diff(g, X) + (a - om*sp.exp(-X))*g
Hal = lambda g, a: -sp.diff(g, X, 2) + (om**2*sp.exp(-2*X) - (2*a + 1)*om*sp.exp(-X) + jq**2*Bq)*g
rep("Morse factorization H_a = D*D + j^2B - a^2", sp.simplify(Dst(Dal(f, al_), al_) + (jq**2*Bq - al_**2)*f - Hal(f, al_)) == 0)
rep("Morse factorization H_{a-1} = DD* + j^2B - a^2", sp.simplify(Dal(Dst(f, al_), al_) + (jq**2*Bq - al_**2)*f - Hal(f, al_ - 1)) == 0)

# ---------------- one cell (Lemma 5.1)
t = sp.symbols('t', positive=True)
rep("cell integrals 3/8 and 15/16",
    sp.integrate(1 - t, (t, 0, sp.Rational(3, 2))) == sp.Rational(3, 8) and
    sp.simplify(sp.integrate(sp.log(sp.Rational(3, 2)/t)*(1 - t), (t, 0, sp.Rational(3, 2))) - sp.Rational(15, 16)) == 0)
for d in (40, 200):
    A = (d**-0.5 + 2*d**-4.5)**2; B = d**-9.0; epsR, cR = 0.5, 0.05
    rho = lambda x: A*(np.exp(-x) - np.exp(-2*x)) - B
    tm = np.roots([A, -A, B]).min(); XR = -np.log(tm); Xc = -np.log(1.5)
    sol = solve_ivp(lambda x, yv: [yv[1], -rho(x)*yv[0]], [XR, Xc], [1.0, epsR*A**5], rtol=1e-12, atol=1e-30, dense_output=True)
    rc, vc = sol.y[0, -1], sol.y[1, -1]
    xs = np.linspace(Xc, XR, 4000); vv = sol.sol(xs)[1]
    sol2 = solve_ivp(lambda x, yv: [yv[1], -rho(x)*yv[0]], [XR, XR + cR*A**-4], [1.0, epsR*A**5], rtol=1e-10, atol=1e-30, max_step=cR*A**-4/2000)
    rep(f"Lemma 5.1 numerics, d={d}: r_X(X_c)~3A/8, r(X_c)~1-15A/16, r_X>0, r_X~A^5 on long cap",
        abs(vc/(3*A/8) - 1) < 3*A and abs((1 - rc)/(15*A/16) - 1) < 3*A and vv.min() > 0
        and 0.5*epsR < sol2.y[1].min()/A**5 and sol2.y[1].max()/A**5 < 5,
        f"ratios {vc/(3*A/8):.4f} {(1-rc)/(15*A/16):.4f}; long cap r_X/A^5 in [{sol2.y[1].min()/A**5:.2f},{sol2.y[1].max()/A**5:.2f}]")
n_ = sp.symbols('n', positive=True)
rep("log(mu_{n+1} R_n): -2(n+1)^2 + 4n^2 = 2n^2 + O(n)", sp.expand(-2*(n_ + 1)**2 + 4*n_**2 - 2*n_**2) == -4*n_ - 2)
kk, mm, nn = sp.symbols('k m n', integer=True)
rep("sum formula in (rm17)", sp.simplify(2*sp.summation(nn**2, (nn, mm, kk - 1))
    - (sp.Rational(2, 3)*(kk**3 - mm**3) - (kk**2 - mm**2) + sp.Rational(1, 3)*(kk - mm))) == 0)

# ---------------- gauge (Lemma 5.3), state on a join (js7), connectors (sp1)
wy = sp.Function('w')(y); Vy = sp.Function('V')(y); uy = sp.exp(j**2*y)*Vy
r2L = wy*sp.diff(uy, y, 2) + (sp.diff(wy, y) - wy)*sp.diff(uy, y) - j**2*sp.diff(wy, y)*uy
pj = wy*sp.exp((2*j**2 - 1)*y)
rep("Lemma 5.3: gauge identity", sp.simplify(r2L - sp.exp(j**2*y)*wy/pj*(sp.diff(pj*sp.diff(Vy, y), y) + j**2*(j**2 - 1)*pj*Vy)) == 0)
ur = sp.Function('u')(r_); wr = sp.Function('w')(r_)
u2 = sp.solve(sp.Eq(sp.diff(wr*sp.diff(ur, r_), r_) - j**2*sp.diff(wr, r_)/r_*ur, 0), sp.diff(ur, r_, 2))[0]
zeta = r_*sp.diff(ur, r_)/j**2 - ur
rep("(js7): (w zeta)' = -(j^2-1) w u'/j^2 on solutions",
    sp.simplify(sp.diff(wr*zeta, r_).subs(sp.diff(ur, r_, 2), u2) + (j**2 - 1)*wr*sp.diff(ur, r_)/j**2) == 0)
fy = sp.Function('f')(y); ky = sp.Function('k')(y)
phi_yy_over_phi = sp.diff(ky, y) + ky**2
wyy = sp.exp(y + fy)
L2 = (wyy*phi_yy_over_phi + (sp.diff(wyy, y) - wyy)*ky - 4*sp.diff(wyy, y))/wyy
sol_f = sp.solve(sp.Eq(L2, 0), sp.diff(fy, y))[0]
rep("Lemma 6.1: f_y = (k^2 + k_y - 4)/(4-k)", sp.simplify(sol_f - (ky**2 + sp.diff(ky, y) - 4)/(4 - ky)) == 0)

# ---------------- matching algebra (Section 6.6-6.7)
t1, t2, d11, d12, d22 = sp.symbols('t1 t2 d11 d12 d22', real=True)
A_ = sp.diag(sp.cos(t1), sp.cos(t2)); B_ = sp.diag(sp.sin(t1), sp.sin(t2)); Db = sp.Matrix([[d11, d12], [d12, d22]])
K = A_*Db - B_; K1 = A_ + B_*Db
z = lambda M: sp.simplify(M) == sp.zeros(2, 2)
rep("matching identities KA=AK^T, K^T K1 = K1^T K, K1 K^-1 A - B = K^-T",
    z(K*A_ - A_*K.T) and z(K.T*K1 - K1.T*K) and z(K1*K.inv()*A_ - B_ - K.inv().T))
rep("middle matrix of (tm11) symmetric", z(K.inv()*A_ - (K.inv()*A_).T) and z(K1*K.inv() - (K1*K.inv()).T))
om_ = sp.Function('omega')(r_); ph = sp.Function('phi')(r_)
integrand = ph*(sp.diff(om_*sp.diff(ph, r_), r_) - 4*sp.diff(om_, r_)*ph/r_) \
    - om_*(-sp.diff(ph, r_)**2 + 8*ph*sp.diff(ph, r_)/r_ - 4*ph**2/r_**2)
rep("(ct-positive-shape): integrands differ by an exact derivative",
    sp.simplify(integrand - sp.diff(om_*ph*sp.diff(ph, r_) - 4*om_*ph**2/r_, r_)) == 0)

# ---------------- finite model (Section 3.3)
e2 = 2e-4
sol = solve_ivp(lambda x, yv: [yv[1], -e2*x*(1 - x)*yv[0]], [0, 2], [1, .1], rtol=1e-12, atol=1e-14, dense_output=True)
solm = solve_ivp(lambda x, yv: [yv[1], -e2*x*(1 - x)*yv[0]], [0, -1], [1, .1], rtol=1e-12, atol=1e-14, dense_output=True)
rr = np.concatenate([sol.sol(np.linspace(0, 2, 500)), solm.sol(np.linspace(0, -1, 500))], axis=1)
rep("finite model: R<1.21, r>0.89, |r_X - 0.1|<0.001", rr[0].max() < 1.21 and rr[0].min() > .89 and np.abs(rr[1] - .1).max() < 1e-3,
    f"r in [{rr[0].min():.4f},{rr[0].max():.4f}], max|r_X-.1|={np.abs(rr[1]-.1).max():.2e}")
js = np.arange(1, 2000001)
rep("finite model: |sin(jT)| >= 1/(320000 j), j <= 2e6", np.min(np.abs(np.sin(js*np.sqrt(2)*np.pi/800))*320000*js) >= 1,
    f"min ratio={np.min(np.abs(np.sin(js*np.sqrt(2)*np.pi/800))*320000*js):.1f}")

# ---------------- mass-resistance chain (Lemma 5.6): exact transfer vs. the recurrence
mp.mp.dps = 50
Lam = mp.mpf(12)
def chain(Ncells, a=mp.mpf('0.03'), b=mp.mpf('0.03')):
    cells = []
    for n in range(Ncells):
        Pn = mp.mpf(10)**(-3*n)            # density on I_n
        pn = Pn*mp.mpf(10)**(-6)           # density on J_n (much smaller)
        cells.append((Pn, a, pn, b))
    return cells
def transfer(p, L):
    s = mp.sqrt(Lam)
    return mp.matrix([[mp.cos(s*L), mp.sin(s*L)/(s*p)], [-s*p*mp.sin(s*L), mp.cos(s*L)]])  # state (V, p V')
cells = chain(14)
mu = [P*a for P, a, p, b in cells]; R = [b/p for P, a, p, b in cells]; nu = [p*b for P, a, p, b in cells]; RI = [a/P for P, a, p, b in cells]
eta = max(max(Lam*mu[n]*RI[n] + Lam*nu[n]*R[n] for n in range(14)), max(nu[n]/min(mu[n], mu[n+1]) for n in range(13)))
Kc = min(min(Lam*mu[n]*R[n] for n in range(14)), min(Lam*mu[n+1]*R[n] for n in range(13)))
# decaying solution: Dirichlet wall at the last node, integrate backwards
st = mp.matrix([0, 1]); vals = [mp.mpf(0)]
for P, a, p, b in reversed(cells):
    st = mp.inverse(transfer(p, b))*st; st = mp.inverse(transfer(P, a))*st; vals.append(st[0])
vals = vals[::-1]                         # node values a_0 .. a_14 (a_14 = 0 at the wall)
dev = []
for n in range(0, 9):
    ratio = vals[n+1]/vals[n]; pred = -1/(Lam*mu[n+1]*R[n]); dev.append(abs(ratio/pred - 1))
rep("Lemma 5.6 on an exact piecewise-constant chain: a_{n+1}/a_n = -(1+O(eta+1/K))/(Lam mu_{n+1} R_n)",
    max(dev) < 5*(eta + 1/Kc) and all(vals[n]*vals[n+1] < 0 for n in range(9)),
    f"eta={mp.nstr(eta,3)}, 1/K={mp.nstr(1/Kc,3)}, max dev={mp.nstr(max(dev),3)}")
print("\nALL PART II CHECKS PASSED" if ok else "\nSOME CHECK FAILED")
