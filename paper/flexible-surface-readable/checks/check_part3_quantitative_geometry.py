"""Machine checks for the quantitative estimates of Sections 7-10 (third round).

These are the explicit identities, exponents and elementary inequalities behind
the lemmas on root collars, reference charts, positive coordinates, the Moser
estimates, the commutator lemma and the weighted primitive.
"""
import sympy as sp, mpmath as mp, numpy as np
from fractions import Fraction as Fr
ok = True
def rep(name, good, info=""):
    global ok
    ok &= bool(good)
    print(f"{'PASS' if good else 'FAIL'}  {name:74s} {info}")

# ---------------------------------------------------------------- roots of a Morse cell
mp.mp.dps = 150
worst = []
for d in (5, 12, 50, 1000, 10**6 + 3):
    sA = mp.mpf(d)**-0.5 + 2*mp.mpf(d)**-4.5; A = sA**2; B = mp.mpf(d)**-9
    disc = mp.sqrt(1 - 4*B/A); tL = (1 + disc)/2; tR = (1 - disc)/2       # t = e^{-X}
    rhoX = lambda t: A*(-t + 2*t*t)                                        # d rho / dX
    worst.append((abs(tL - 1)/(B/A), tR/(B/A), abs(rhoX(tL))/A, abs(rhoX(tR))/B))
good = all(0.5 < a < 2.1 and 0.5 < b < 2.1 and 0.5 < c < 2 and 0.5 < e < 2 for a, b, c, e in worst)
rep("Morse roots: e^{-X_L}=1+O(B/A), e^{-X_R}~B/A, |rho_X|~A and ~B", good,
    "ratios in [%.3f, %.3f]" % (min(min(w) for w in worst), max(max(w) for w in worst)))

# root coefficient c_i(0)^2 = |rho_X| / v^3 on an integrated cell
d = 12; sA = d**-0.5 + 2*d**-4.5; A = sA**2; B = float(d)**-9; delta = 0.2
rho = lambda X: A*(np.exp(-X) - np.exp(-2*X)) - B
tL = (1 + np.sqrt(1 - 4*B/A))/2; tR = (1 - np.sqrt(1 - 4*B/A))/2
XL, XR = -np.log(tL), -np.log(tR)
from scipy.integrate import solve_ivp
sol = solve_ivp(lambda X, y: [y[1], -rho(X)*y[0]], [XR, XL - 0.3], [1.0, delta*A**5],
                rtol=1e-12, atol=1e-18, dense_output=True)
errs = []
for Xroot, sgn in ((XL, +1), (XR, -1)):
    r0, v0root = sol.sol(Xroot)
    rhoXroot = abs(A*(-np.exp(-Xroot) + 2*np.exp(-2*Xroot)))
    target = rhoXroot/v0root**3
    for h in (1e-3, 1e-4):
        X = Xroot + sgn*h*min(1.0, v0root/(abs(rhoXroot)*10 + 1e-300))  # a point just inside the component
        r, v = sol.sol(X); x = abs(r - r0)
        errs.append(abs((rho(X)/v**2)/x/target - 1))
rep("root coefficient: v0^2/x -> |rho_X|/r_X^3 at both roots of a cell", max(errs) < 2e-3, f"max rel err={max(errs):.1e}")
vL = sol.sol(XL)[1]
rep("r_X at the left root is comparable to A (backward integration)", 0.1 < vL/A < 10, f"r_X(X_L)/A={vL/A:.3f}")

# ---------------------------------------------------------------- exponent bookkeeping (powers of A_n)
cL, cR, dl = Fr(-1), Fr(-3), Fr(20)            # c_L(0) ~ A^-1, c_R(0) ~ A^-3, collar ~ A^20
v0_sup = dl/2 + cL                              # v0 = sqrt(x) c_L on the control support
books = {
 "c_L(0)^2 = A / A^3":                       (2*cL == 1 - 3),
 "c_R(0)^2 = A^9 / A^15":                    (2*cR == 9 - 15),
 "v0 ~ A^9 on the control support":          (v0_sup == 9),
 "|w'/w| = r v0^2 ~ A^18":                   (2*v0_sup == 18),
 "pairing ~ delta^{-1/2}/c_L ~ A^-9":        (-dl/2 - cL == -9),
 "|d^k chi_n| ~ A^{9-20k}":                  (9 - dl*1 == -11),
 "|kappa chi'| / |w'/w| ~ |kappa| A^-29":    ((9 - dl) - 2*v0_sup == -29),
 "model distance of the collar: A^19, A^15": (dl - 1 == 19 and dl - 5 == 15),
 "rho >= A^24 outside the collars":          (min(1 + 19, 9 + 15) == 20 and max(1 + 19, 9 + 15) == 24),
 "v0 >= A^11 outside the collars":           (Fr(24, 2) - 1 == 11),
 "collar increment of xi: A^{20} c_R^{2/3} = A^18": (dl + Fr(2, 3)*cR == 18),
 "collar / (r_X at right root) = A^15":      (dl - 5 == 15),
}
rep("exponent bookkeeping for the root collars and controls", all(books.values()),
    "" if all(books.values()) else str([k for k, v in books.items() if not v]))

# ---------------------------------------------------------------- travel-angle control pairing
c0, a_, rL, dlt = 3.0, 0.5, 1.0, 1e-3
phi = lambda z: np.where((z > 1) & (z < 2), np.exp(-1/np.maximum((z - 1)*(2 - z), 1e-300)), 0.0)
xs = np.linspace(0, 4*dlt, 800001)[1:]; dx = xs[1] - xs[0]
cfun = lambda x: c0*(1 + x/a_); v0 = lambda x: np.sqrt(x)*cfun(x); rr = rL + xs
f = phi(xs/dlt); fp = np.gradient(f, dx)
Tfun = lambda t: np.sum(np.sqrt(np.maximum(v0(xs)**2 - t*fp/rr, 0.0)))*dx
tt = 1e-7
fd = (Tfun(tt) - Tfun(-tt))/(2*tt)
direct = np.sum(-fp/(2*rr*v0(xs)))*dx
ibp = 0.5*np.sum(np.gradient(1/(rr*v0(xs)), dx)*f)*dx
zs = np.linspace(1, 2, 200001); lead = -dlt**-0.5/(4*rL*c0)*np.sum(zs**-1.5*phi(zs))*(zs[1] - zs[0])
rep("D T[f] = -int f'/(2 r v0) = (1/2) int ((r v0)^{-1})' f   (finite difference)",
    abs(fd/direct - 1) < 1e-5 and abs(ibp/direct - 1) < 1e-4, f"rel errs {abs(fd/direct-1):.1e}, {abs(ibp/direct-1):.1e}")
rep("leading term -(delta^{-1/2}/(4 r_L c_L(0))) int_1^2 z^{-3/2} phi, error O(delta/a)",
    abs(direct/lead - 1) < 20*dlt/a_, f"rel err={abs(direct/lead-1):.1e}  (delta/a={dlt/a_:.0e})")

# ---------------------------------------------------------------- the regularized root coordinate
x, c0s, c1s, z = sp.symbols('x c0 c1 zeta', positive=True)
cs = c0s + c1s*x
sigma = sp.integrate(sp.sqrt(z)*(c0s + c1s*z), (z, 0, x))
g = sp.Rational(3, 2)*sp.integrate(sp.sqrt(z)*(c0s + c1s*x*z), (z, 0, 1))
xi = x*g**sp.Rational(2, 3)
rep("xi = (3 sigma/2)^{2/3} = x [ (3/2) int_0^1 sqrt(z) c(xz) dz ]^{2/3}",
    sp.simplify(xi**sp.Rational(3, 2) - sp.Rational(3, 2)*sigma) == 0)
rep("xi (xi_x)^2 = x c(x)^2  and  xi_x(0) = c(0)^{2/3}",
    sp.simplify(xi*sp.diff(xi, x)**2 - x*cs**2) == 0 and sp.simplify(sp.diff(xi, x).subs(x, 0) - c0s**sp.Rational(2, 3)) == 0)
xr = sp.symbols('x', real=True)
gr = c0s + sp.Rational(3, 5)*c1s*xr
xir = xr*gr**sp.Rational(2, 3)
rep("the identity xi xi_x^2 = x c^2 continues to x<0 (positive side of the root)",
    sp.simplify((xir*sp.diff(xir, xr)**2 - xr*(c0s + c1s*xr)**2).subs({c0s: 2, c1s: sp.Rational(1, 3), xr: -sp.Rational(1, 7)})) == 0)

# ---------------------------------------------------------------- positive comparison coordinates
r, jf = sp.symbols('r j', positive=True)
w = sp.Function('w')(r); h = sp.Function('h')(r); y = sp.Function('y')(r); U = sp.Function('U')(r)
jac = sp.diff(y, r)
Lmode = lambda u: sp.diff(w*sp.diff(u, r), r) - jf**2*sp.diff(w, r)/r*u        # (w u_r)_r + (w'/r) u_thth on mode j
lhs = -(h/jac)*Lmode(h*U)
a = h**2*w*jac; c = h**2*sp.diff(w, r)/(r*jac); V = -(h/jac)*sp.diff(w*sp.diff(h, r), r)
Uy = sp.diff(U, r)/jac
rhs = -sp.diff(a*Uy, r)/jac + jf**2*c*U + V*U
rep("positive canonical form: -(h/j) L[h U] = -(a U_y)_y + j^2 c U + V U", sp.simplify(sp.expand(lhs - rhs)) == 0)
hc = (w*jac)**sp.Rational(-1, 2)
rep("in a root collar h=(w y_r)^{-1/2} gives a = 1 and c = (w'/(r w)) / y_r^2",
    sp.simplify(hc**2*w*jac - 1) == 0 and sp.simplify(hc**2*sp.diff(w, r)/(r*jac) - sp.diff(w, r)/(r*w*jac**2)) == 0)

# ---------------------------------------------------------------- Q and D in terms of Z
rs, th = sp.symbols('r theta', positive=True)
ws = sp.Function('w')(rs); Zs = sp.Function('Z')(rs, th)
kk = ws + sp.diff(Zs, rs); pp = sp.diff(Zs, th)/rs; Es = 1 + ws**2
Dq = Es*(1 - pp**2) - kk**2; Qq = kk + Es*sp.diff(pp, th)
rep("D = 1 - 2 w Z_r - Z_r^2 - E (Z_th/r)^2  and  Q = w + Z_r + E Z_thth / r",
    sp.simplify(Dq - (1 - 2*ws*sp.diff(Zs, rs) - sp.diff(Zs, rs)**2 - Es*(sp.diff(Zs, th)/rs)**2)) == 0 and
    sp.simplify(Qq - (ws + sp.diff(Zs, rs) + Es*sp.diff(Zs, th, 2)/rs)) == 0)

# ---------------------------------------------------------------- weights: slow variation
xx = sp.symbols('x', positive=True)
dlogE = sp.diff(xx**sp.Rational(5, 2)*sp.log(sp.E + xx), xx)/(2*xx*(1 + xx))
dlogM = sp.diff(xx**sp.Rational(5, 2)*sp.log(sp.E + xx)**2, xx)/(2*xx*(1 + xx))
rep("D log E_0 -> 0 and D log M -> 0 at the endpoints, |D log H| -> 1",
    sp.limit(dlogE, xx, sp.oo) == 0 and sp.limit(dlogM, xx, sp.oo) == 0 and sp.limit(xx/(1 + xx), xx, sp.oo) == 1)
nsym = sp.symbols('n', positive=True)
ratio = sp.diff(nsym**sp.Rational(5, 2)*sp.log(sp.E + nsym)**2, nsym)/sp.diff(2*nsym**3/3, nsym)
samples = [float(ratio.subs(nsym, 10.0**e_)) for e_ in (2, 4, 6, 8, 10, 12)]
rep("d(log M)/dS -> 0, hence |log M_k - log M_m| <= delta |S_k - S_m| + C_delta",
    sp.limit(ratio, nsym, sp.oo) == 0 and all(samples[i] > samples[i + 1] for i in range(len(samples) - 1)),
    "ratio at n=1e2..1e12: " + ", ".join(f"{v:.2g}" for v in samples))
nn = np.arange(1, 3000, dtype=float); S = 2*nn**3/3
rep("Schur sums: sup_k sum_m exp(-|S_k - S_m|/8) is finite",
    max(np.sum(np.exp(-np.abs(S[k] - S[:400])/8)) for k in range(400)) < 3)

# ---------------------------------------------------------------- Moser / Gagliardo-Nirenberg
rng = np.random.default_rng(1); Nn = 2048; thg = np.linspace(0, 2*np.pi, Nn, endpoint=False)
def randfun(K):
    kv = np.arange(1, K + 1); a1 = rng.normal(size=K)/kv**rng.uniform(0.5, 3); b1 = rng.normal(size=K)/kv**rng.uniform(0.5, 3)
    u = sum(a1[i]*np.cos(kv[i]*thg) + b1[i]*np.sin(kv[i]*thg) for i in range(K))
    u1 = sum(-a1[i]*kv[i]*np.sin(kv[i]*thg) + b1[i]*kv[i]*np.cos(kv[i]*thg) for i in range(K))
    u2 = sum(-a1[i]*kv[i]**2*np.cos(kv[i]*thg) - b1[i]*kv[i]**2*np.sin(kv[i]*thg) for i in range(K))
    return u, u1, u2
l2 = lambda f: np.sqrt(np.mean(f**2)*2*np.pi); l4 = lambda f: (np.mean(f**4)*2*np.pi)**0.25
worst1 = worst2 = 0.0
for _ in range(300):
    u, u1, u2 = randfun(rng.integers(1, 40)); v, v1, v2 = randfun(rng.integers(1, 40))
    worst1 = max(worst1, l4(u1)**2/(np.max(np.abs(u))*l2(u2)))
    worst2 = max(worst2, l2(u1*v1)/(np.max(np.abs(u))*l2(v2) + l2(u2)*np.max(np.abs(v))))
rep("||u'||_4^2 <= 3 ||u||_inf ||u''||_2 on the circle (300 random samples)", worst1 <= 3, f"max ratio={worst1:.3f}")
rep("||u' v'||_2 <= (3/2)(||u||_inf ||v''||_2 + ||u''||_2 ||v||_inf)", worst2 <= 1.5, f"max ratio={worst2:.3f}")
worst3 = 0.0
for _ in range(20000):
    th_ = rng.uniform(0, 1); A_ = 1 + rng.exponential(50); u0, u1_ = rng.exponential(1, 2)
    worst3 = max(worst3, (A_*u0)**th_*u1_**(1 - th_)/(u1_ + A_*u0))
    jj_ = float(rng.integers(0, 10**4)); N_ = int(rng.integers(1, 12)); s_ = rng.uniform(0, N_)
    worst3 = max(worst3, float(((mp.mpf(1) + jj_**2)**N_ + A_**2)**(s_/(2*N_))/((mp.mpf(1) + jj_**2)**(s_/2) + A_)))
rep("Young and interpolated-weight inequalities of the commutator lemma", worst3 <= 1 + 1e-12, f"max ratio={worst3:.4f}")

# ---------------------------------------------------------------- commutator identity
n = 24; Lam = np.diag(np.abs(np.arange(-n//2, n//2)).astype(float)); Rm = rng.normal(size=(n, n)) + 1j*rng.normal(size=(n, n))
Cm = Lam@Rm - Rm@Lam; eps = 0.7
Ue = lambda e_: np.diag(np.exp(1j*e_*np.diag(Lam)))
gsn, gsw = np.polynomial.legendre.leggauss(60); ups = 0.5*eps*(gsn + 1); wq = 0.5*eps*gsw
integ = sum(wk*Ue(eps - uk)@Cm@Ue(uk) for uk, wk in zip(ups, wq))
rep("[U_eps, R] = i int_0^eps U_{eps-t} [Lambda,R] U_t dt  (U_eps = exp(i eps Lambda))",
    np.max(np.abs(Ue(eps)@Rm - Rm@Ue(eps) - 1j*integ)) < 1e-9)
s0 = 5; Ls = np.linalg.matrix_power(Lam, s0)
comm = sum(np.linalg.matrix_power(Lam, k)@Cm@np.linalg.matrix_power(Lam, s0 - 1 - k) for k in range(s0))
rep("[Lambda^s, R] = sum_k Lambda^k [Lambda,R] Lambda^{s-1-k}", np.max(np.abs(Ls@Rm - Rm@Ls - comm)) < 1e-6*np.max(np.abs(Ls)))

# ---------------------------------------------------------------- second variation of an inverse lift
tq, s1, s2 = sp.symbols('theta s1 s2', real=True)
a1, b1_, c1_ = sp.sin(2*tq)/5, sp.sin(4*tq)/7, sp.sin(6*tq)/9
hfun = lambda t_: t_ + s1*a1.subs(tq, t_) + s2*b1_.subs(tq, t_) + s1*s2*c1_.subs(tq, t_)
# perturbative inverse to second order: iota = theta + s1 i1 + s2 i2 + s1 s2 i12
i1, i2 = -a1, -b1_
i12 = -(c1_ + sp.diff(a1, tq)*i2 + sp.diff(b1_, tq)*i1)          # formula with h'=1, h''=0 at s=0
iota = tq + s1*i1 + s2*i2 + s1*s2*i12
resid = sp.series(sp.series(hfun(iota) - tq, s1, 0, 2).removeO(), s2, 0, 2).removeO()
resid = sp.expand(resid)
coef = [resid.coeff(s1, i).coeff(s2, j) for i in (0, 1) for j in (0, 1)]
rep("iota_12 = -(h_12 + h_1' iota_2 + h_2' iota_1 + h'' iota_1 iota_2)/h'  (checked at h = id)",
    all(sp.simplify(c_) == 0 for c_ in coef))

# ---------------------------------------------------------------- Fourier convolution with weights
worst4 = 0.0
for _ in range(200):
    K = 64; kk_ = np.arange(-K, K + 1); s_ = rng.integers(1, 6)
    e_ = rng.exponential(1, 2*K + 1)/(1 + np.abs(kk_))**rng.uniform(2, 5); g_ = rng.exponential(1, 2*K + 1)/(1 + np.abs(kk_))**rng.uniform(2, 5)
    conv = np.convolve(e_, g_)                       # indices -2K..2K
    ll = np.arange(-2*K, 2*K + 1); br = lambda q: (1 + q**2)**0.5
    lhs_ = np.sqrt(np.sum(br(ll)**(2*s_)*conv**2))
    rhs_ = 2**s_*(np.sum(e_)*np.sqrt(np.sum(br(kk_)**(2*s_)*g_**2)) + np.sqrt(np.sum(br(kk_)**(2*s_)*e_**2))*np.sum(g_))
    worst4 = max(worst4, lhs_/rhs_)
rep("|| <l>^s (e*g) ||_l2 <= 2^s ( ||e||_l1 ||<k>^s g||_l2 + ||<k>^s e||_l2 ||g||_l1 )", worst4 <= 1, f"max ratio={worst4:.3f}")

print("\nALL QUANTITATIVE-GEOMETRY CHECKS PASSED" if ok else "\nSOME CHECK FAILED")
