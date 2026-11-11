"""Machine checks, Part III of the paper (Sections 7-10), plus one supplement to Part II."""
import sympy as sp, mpmath as mp, numpy as np
ok = True
def rep(name, good, info=""):
    global ok
    ok &= bool(good)
    print(f"{'PASS' if good else 'FAIL'}  {name:70s} {info}")

# ---- supplement: eigenvalues of the Morse model alone stay >= 1/(8 d^5) away from zero
mp.mp.dps = 60
for d in (2, 3, 5, 7, 1001):
    sA = mp.mpf(d)**-0.5 + 2*mp.mpf(d)**-4.5; B = mp.mpf(d)**-9; worst = mp.inf
    for jj in list(range(2, 6001)) + [10**5 + i for i in range(500)]:
        al = (jj*sA - 1)/2; m0 = mp.nint(al - jj*mp.sqrt(B))
        for m in (m0 - 1, m0, m0 + 1):
            if 0 <= m < al: worst = min(worst, abs(jj*jj*B - (al - m)**2))
    rep(f"Morse eigenvalues: |E_(m,j)| >= 1/(8 d^5), d={d}", worst >= 1/(8*mp.mpf(d)**5), f"min*8d^5={mp.nstr(worst*8*mp.mpf(d)**5,5)}")

# ---- weights (Section 7.2)
d_, d0 = sp.symbols('d d0', positive=True)
x = sp.sqrt(sp.log(d0/d_)); ell = d_/(1 + x)
rep("|D x| = 1/(2x(1+x)),  |D log H| = x/(1+x)",
    sp.simplify(ell*sp.diff(x, d_) + 1/(2*x*(1 + x))) == 0 and
    sp.simplify(ell*sp.diff(-sp.Rational(2, 3)*x**3, d_) - x/(1 + x)) == 0)

# ---- return residual: identity and derivative with respect to the chart (Section 7.5)
N = 4096; th = np.linspace(-np.pi, np.pi, N, endpoint=False); T = 0.37
def comp_inv(h):            # inverse of an increasing lift h(theta)=theta+periodic, on the grid
    return lambda yv: np.interp(yv, np.concatenate([h(th) - 2*np.pi, h(th), h(th) + 2*np.pi]),
                                np.concatenate([th - 2*np.pi, th, th + 2*np.pi]))
hL = lambda t: t + 0.05*np.sin(2*t) + 0.02*np.sin(4*t)                       # odd, pi-equivariant
f = lambda t: t - T + 0.03*np.cos(2*t) + 0.02*np.sin(2*t) + 0.01*np.cos(4*t)   # near R_{-T}
finv = comp_inv(f)
def charts(hLfun):
    ht = lambda t: hLfun(finv(t)) - T                 # \tilde h_R = R_{-T} h_L f^{-1}
    hR = lambda t: 0.5*(ht(t) - ht(-t))               # odd part
    ev = lambda t: 0.5*(ht(t) + ht(-t))               # even part
    hRinv = comp_inv(hR)
    e = lambda t: ev(hRinv(t))
    return ht, hR, e
ht, hR, e = charts(hL)
tt = np.linspace(-3, 3, 400)
lhs = hR(f(tt)); lhs = lhs + e(lhs)                   # (id + e) h_R f
rhs = hL(tt) - T                                       # R_{-T} h_L
rep("return identity (id+e) h_R f h_L^{-1} = R_{-T}", np.max(np.abs(lhs - rhs)) < 1e-6, f"max err={np.max(np.abs(lhs-rhs)):.1e}")
psi = lambda t: 0.3*np.sin(2*t) - 0.2*np.sin(6*t); dpsi = lambda t: 0.6*np.cos(2*t) - 1.2*np.cos(6*t)
s = 1e-4
_, _, ep = charts(lambda t: hL(t) + s*psi(hL(t))); _, _, em = charts(lambda t: hL(t) - s*psi(hL(t)))
fd = (ep(tt) - em(tt))/(2*s)
E = lambda g: lambda t: 0.5*(g(t) + g(-t)); O = lambda g: lambda t: 0.5*(g(t) - g(-t))
de = lambda t: (e(t + 1e-4) - e(t - 1e-4))/2e-4
gs = np.polynomial.legendre.leggauss(12); nodes = 0.5*(gs[0] + 1); wts = 0.5*gs[1]
MT = E(lambda t: psi(t + T))
Q1 = E(lambda t: e(t)*sum(wk*dpsi(t + T + sk*e(t)) for sk, wk in zip(nodes, wts)))
Q2 = lambda t: de(t)*O(lambda t_: psi(t_ + T + e(t_)))(t)
formula = MT(tt) + Q1(tt) - Q2(tt)
rep("chart derivative: D_h e[psi] = M_T psi + Q_h(e,psi)", np.max(np.abs(fd - formula)) < 2e-4,
    f"max err={np.max(np.abs(fd-formula)):.1e} (|e|max={np.max(np.abs(e(tt))):.2e})")
jj = 6; g = lambda t: np.sin(jj*t)
rep("M_T sin(j theta) = sin(jT) cos(j theta)", np.max(np.abs(E(lambda t: g(t + T))(tt) - np.sin(jj*T)*np.cos(jj*tt))) < 1e-12)

# ---- travel coordinates: Jacobian (Section 7.6)
Ut, Vt, cp, cm = sp.symbols('U_theta V_theta c_plus c_minus', real=True)
Ur, Vr = -cp*Ut, -cm*Vt
jac = sp.Matrix([[(Vr - Ur)/2, (Vt - Ut)/2], [(Ur + Vr)/2, (Ut + Vt)/2]]).det()
rep("det d(sigma,phi)/d(r,theta) = v U_theta V_theta", sp.simplify(jac - (cp - cm)/2*Ut*Vt) == 0)
# root flow
xx, tq, zeta = sp.symbols('x t zeta', positive=True)
rep("root flow: x'=x t^2 turns dTheta/dx' = d + sqrt(x') c0 into (fixed-strip-root-flow)",
    sp.simplify(sp.diff(xx*tq**2, tq)*sp.sqrt(xx*tq**2) - 2*xx**sp.Rational(3, 2)*tq**2) == 0)
# transmission in the middle
sig, Tt = sp.symbols('sigma T', positive=True)
xiL = (sp.Rational(3, 2)*sig)**sp.Rational(2, 3); xiR = (sp.Rational(3, 2)*(Tt - sig))**sp.Rational(2, 3)
dlt = sp.Function('delta')(sig); WL = sp.Function('W_L'); WR = sp.Function('W_R')
aL, aR = dlt/sp.sqrt(xiL), dlt/sp.sqrt(xiR)
rep("d xi_L/d sigma = xi_L^{-1/2}", sp.simplify(sp.diff(xiL, sig) - xiL**sp.Rational(-1, 2)) == 0)
jump = sp.simplify((sp.diff(sp.log(aR), sig) - sp.diff(sp.log(aL), sig)).subs(sig, Tt/2))
xic = (sp.Rational(3, 4)*Tt)**sp.Rational(2, 3)
rep("d_sigma log alpha_R - d_sigma log alpha_L = xi_c^{-3/2} at the middle", sp.simplify(jump - xic**sp.Rational(-3, 2)) == 0)
W, WLx, WRx, dla = sp.symbols('W W_Lxi W_Rxi dlogalphaL', real=True)
# continuity of d_sigma (alpha^{-1/2} W): -1/2 dlog(alpha) W + (dxi/dsigma) W_xi
eq = sp.Eq(-sp.Rational(1, 2)*dla*W + xic**sp.Rational(-1, 2)*WLx,
           -sp.Rational(1, 2)*(dla + xic**sp.Rational(-3, 2))*W - xic**sp.Rational(-1, 2)*WRx)
rep("transmission matrix (fixed-strip-cut): W_Rxi = -W/(2 xi_c) - W_Lxi", sp.simplify(sp.solve(eq, WRx)[0] - (-W/(2*xic) - WLx)) == 0)
# canonical form: conjugation removes first-order terms
xi, ph = sp.symbols('xi varphi', real=True)
al = sp.Function('alpha')(xi, ph); Wf = sp.Function('W')(xi, ph)
u = Wf/sp.sqrt(al)
op = sp.diff(al*sp.diff(u, xi), xi) - sp.diff(al*xi*sp.diff(u, ph), ph)
Vpot = -(sp.diff(sp.sqrt(al), xi, 2) - xi*sp.diff(sp.sqrt(al), ph, 2))/sp.sqrt(al)
rep("canonical form: alpha^{-1/2} div(alpha diag(1,-xi) grad(alpha^{-1/2} W)) = (d_xi^2 - xi d_phi^2 + V) W",
    sp.simplify(op/sp.sqrt(al) - (sp.diff(Wf, xi, 2) - xi*sp.diff(Wf, ph, 2) + Vpot*Wf)) == 0)

# ---- cubic estimate (Lemma 8.2): the two integral identities, as exact derivatives
yv = sp.symbols('y', real=True); jn = sp.symbols('j', real=True)
a = sp.Function('a')(yv); c = sp.Function('c')(yv); Vp = sp.Function('V')(yv); uu = sp.Function('u')(yv)
d = yv*(1 - yv)
Pu = -sp.diff(a*sp.diff(uu, yv), yv) + jn**2*c*uu + Vp*uu
lhs = a*sp.diff(d*uu, yv)**2 + jn**2*c*d**2*uu**2 - Pu*d**2*uu - a*sp.diff(d, yv)**2*uu**2 + Vp*d**2*uu**2
exact = -sp.diff(a*sp.diff(uu, yv)*d**2*uu, yv)       # boundary term, vanishes since d=0 at the ends
rep("Lemma 8.2 step 1: integrand identity (real u)", sp.simplify(lhs + exact) == 0)
ut = d**2*uu
rep("Lemma 8.2 step 2: P(d^2 u) = d^2 P u - 2a(d^2)'u' - (a(d^2)')'u",
    sp.simplify((-sp.diff(a*sp.diff(ut, yv), yv) + jn**2*c*ut + Vp*ut) - (d**2*Pu - 2*a*sp.diff(d**2, yv)*sp.diff(uu, yv) - sp.diff(a*sp.diff(d**2, yv), yv)*uu)) == 0)
q0 = sp.Function('q')(yv); vv = sp.Function('v')(yv)
F1 = -sp.diff(vv, yv, 2) + jn**2*q0*vv
lhs2 = sp.diff(vv, yv, 2)**2 + jn**4*q0**2*vv**2 + 2*jn**2*q0*sp.diff(vv, yv)**2 - F1**2 - jn**2*sp.diff(q0, yv, 2)*vv**2
exact2 = sp.diff(2*jn**2*q0*vv*sp.diff(vv, yv) - jn**2*sp.diff(q0, yv)*vv**2, yv)   # vanishes for v=0 at the ends
rep("Lemma 8.2 step 2: second identity (real v, zero trace)", sp.simplify(lhs2 - exact2) == 0)
s_ = sp.symbols('s', positive=True)
Ftest = yv**3*sp.exp(yv) + yv**5*sp.cos(yv)          # F(0)=F'(0)=F''(0)=0
rem = sp.Rational(1, 2)*sp.integrate((1 - s_)**2*sp.diff(Ftest, yv, 3).subs(yv, s_*yv), (s_, 0, 1))
rep("division by y^3: F(y)/y^3 = (1/2) int_0^1 (1-t)^2 F'''(ty) dt",
    abs(float((rem - Ftest/yv**3).subs(yv, 0.37))) < 1e-12)

# ---- Section 9: reference mean row
ws, Zr = sp.symbols('w Z_r', positive=True)
speed = ws*sp.sqrt(1 - 2*ws*Zr - Zr**2)/(ws + Zr)
rep("(rewrite-reference-circle-row): d log v / dZ_r at 0 = -(1+w^2)/w",
    sp.simplify(sp.diff(sp.log(speed), Zr).subs(Zr, 0) + (1 + ws**2)/ws) == 0)
# travel-angle control: delta v0 = -f'/(2 r v0)
rr = sp.symbols('r', positive=True); tpar = sp.symbols('t', real=True)
wst = sp.Function('w')(rr); ff = sp.Function('f')(rr)
v2 = -sp.diff(wst*sp.exp(tpar*ff), rr)/(rr*wst*sp.exp(tpar*ff))
rep("Lemma 7.6: delta(v0^2) = -f'/r", sp.simplify(sp.diff(v2, tpar).subs(tpar, 0) + sp.diff(ff, rr)/rr) == 0)
print("\nALL PART III CHECKS PASSED" if ok else "\nSOME CHECK FAILED")
