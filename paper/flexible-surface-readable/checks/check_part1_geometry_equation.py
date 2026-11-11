"""Machine checks, Part I of the paper (Sections 2, 3) and Appendix A."""
import sympy as sp, random
random.seed(1)
r, th, eps = sp.symbols('r theta epsilon', real=True)
ok = True
def report(name, val, tol=1e-9):
    global ok
    good = abs(val) < tol
    ok &= good
    print(f"{'PASS' if good else 'FAIL'}  {name:62s} max|err| = {float(abs(val)):.2e}")

# ---- test functions (generic, not solutions of anything)
w = sp.Rational(3,10) + sp.Rational(1,5)*r**2 - sp.Rational(1,20)*r**3
z = (sp.Rational(1,3)*r**2 + sp.Rational(1,15)*sp.sin(2*th)*r**2
     + sp.Rational(1,40)*r**3*sp.cos(4*th) + sp.Rational(1,50)*sp.exp(r/2)*sp.cos(2*th))
eta = sp.Rational(1,7)*r*sp.cos(2*th) + sp.Rational(1,9)*r**2*sp.sin(4*th) + sp.Rational(1,5)*sp.exp(-r)
E = 1 + w**2
pts = [(1.0+0.3*random.random(), 6.28*random.random()) for _ in range(6)]
def maxerr(expr):
    return max(abs(complex(expr.subs({r:a, th:b}).evalf(30))) for a,b in pts)

def jets(zz):
    k = sp.diff(zz, r); p = sp.diff(zz, th)/r
    D = E*(1-p**2) - k**2; Q = k + E*sp.diff(p, th)
    return k, p, D, Q
def gauss_curv(g11, g12, g22):
    """Brioschi formula for a metric g11 dr^2 + 2 g12 dr dth + g22 dth^2."""
    Eu, Ev = sp.diff(g11, r), sp.diff(g11, th)
    Fu, Fv = sp.diff(g12, r), sp.diff(g12, th)
    Gu, Gv = sp.diff(g22, r), sp.diff(g22, th)
    Evv = sp.diff(g11, th, 2); Fuv = sp.diff(g12, r, th); Guu = sp.diff(g22, r, 2)
    M1 = sp.Matrix([[-Evv/2 + Fuv - Guu/2, Eu/2, Fu - Ev/2],
                    [Fv - Gu/2, g11, g12],
                    [Gv/2, g12, g22]])
    M2 = sp.Matrix([[0, Ev/2, Gu/2], [Ev/2, g11, g12], [Gu/2, g12, g22]])
    return (M1.det() - M2.det())/(g11*g22 - g12**2)**2

k, p, D, Q = jets(z)
zr, zt = sp.diff(z, r), sp.diff(z, th)
g11, g12, g22 = E - zr**2, -zr*zt, r**2 - zt**2
Kbar = gauss_curv(g11, g12, g22)

# (a) det gbar = r^2 D, 1-|dz|_g^2 = D/E
report("det(gbar) = r^2 D", maxerr(g11*g22 - g12**2 - r**2*D))
sigma = zr**2/E + zt**2/r**2
report("1 - |dz|_g^2 = D/E", maxerr(1 - sigma - D/E))

# (b) Prop 3.1(ii): r N = D^{-3/2}[...] with N = -sqrt(D) K(gbar)
Nbr = Q*sp.diff(k, r) - E*r*sp.diff(p, r)**2 - sp.diff(E, r)/2*(1 - p**2 + k*sp.diff(p, th))
rN = Nbr/D**sp.Rational(3,2)
report("Prop 3.1(ii): -sqrt(D) K(gbar) = N_h(z)", maxerr(-sp.sqrt(D)*Kbar - rN/r))

# (c) Lemma 2.2: K(gbar) = (K_g(1-sigma) - det_g Hess_g z)/(1-sigma)^2
Kg = sp.diff(E, r)/(2*r*E**2)
H11 = sp.diff(z, r, 2) - sp.diff(E, r)/(2*E)*zr
H12 = sp.diff(z, r, th) - zt/r
H22 = sp.diff(z, th, 2) + r/E*zr
detg = (H11*H22 - H12**2)/(E*r**2)
report("Lemma 2.2 (Darboux curvature formula)", maxerr(Kbar - (Kg*(1-sigma) - detg)/(1-sigma)**2))
report("K_g = E'/(2 r E^2) (Brioschi)", maxerr(gauss_curv(E, 0, r**2) - Kg))

# (d) connection form: structure equations and d(alpha)
eta1_r = sp.sqrt(D)/sp.sqrt(1-p**2)                     # eta1 = eta1_r dr
eta2_r, eta2_t = -k*p/sp.sqrt(1-p**2), r*sp.sqrt(1-p**2)
al_r = k*sp.diff(p, r)/((1-p**2)*sp.sqrt(D))
al_t = (1 + k*sp.diff(p, th)/(1-p**2))/sp.sqrt(D)
# d eta1 = alpha ^ eta2 ; coefficient of dr^dth
report("structure eq. d eta1 = alpha ^ eta2", maxerr(-sp.diff(eta1_r, th) - (al_r*eta2_t - al_t*eta2_r)))
report("structure eq. d eta2 = -alpha ^ eta1", maxerr(sp.diff(eta2_t, r) - sp.diff(eta2_r, th) - al_t*eta1_r))
report("d alpha = r N dr^dth", maxerr(sp.diff(al_t, r) - sp.diff(al_r, th) - rN))

# (e) linearization in divergence form, and determinant identity
a = Q/D**sp.Rational(3,2); b = -E*sp.diff(p, r)/D**sp.Rational(3,2)
c = (E*sp.diff(k, r) - sp.diff(E, r)*k/2)/(r*D**sp.Rational(3,2))
def rN_of(zz):
    kk, pp, DD, QQ = jets(zz)
    return (QQ*sp.diff(kk, r) - E*r*sp.diff(pp, r)**2 - sp.diff(E, r)/2*(1 - pp**2 + kk*sp.diff(pp, th)))/DD**sp.Rational(3,2)
lin = sp.diff(rN_of(z + eps*eta), eps).subs(eps, 0)
div = sp.diff(a*sp.diff(eta, r) + b*sp.diff(eta, th), r) + sp.diff(b*sp.diff(eta, r) + c*sp.diff(eta, th), th)
report("Prop 3.1(iii): r D_z N eta = div form", maxerr(lin - div))
K0 = w*sp.diff(w, r)/r
report("Prop 3.1(iv): ac-b^2 = K0/D^2 + E D^{-3/2} N", maxerr(a*c - b**2 - K0/D**2 - E/D**sp.Rational(3,2)*rN/r))
B = E/(r*Q); cbar = c - B*rN
report("Lemma 3.4: a cbar - b^2 = K0/D^2", maxerr(a*cbar - b**2 - K0/D**2))
# variation of alpha: d(theta)-component  = a eta_r + b eta_th + d_theta(B1 dp)
def al_t_of(zz):
    kk, pp, DD, QQ = jets(zz); return (1 + kk*sp.diff(pp, th)/(1-pp**2))/sp.sqrt(DD)
B1 = k/((1-p**2)*sp.sqrt(D))
dal_t = sp.diff(al_t_of(z + eps*eta), eps).subs(eps, 0)
report("eq. (conn-exact-variation), d theta component",
       maxerr(dal_t - (a*sp.diff(eta, r) + b*sp.diff(eta, th) + sp.diff(B1*sp.diff(eta, th)/r, th))))
# characteristic speed
report("char. speed: sqrt(b^2-a cbar)/a = sqrt(-w w'/r) sqrt(D)/Q  (squares)",
       maxerr((b**2 - a*cbar)/a**2 - (-w*sp.diff(w, r)/r)*D/Q**2))
# linearization at the radial height
u = sp.Function('u')(r, th); ws = sp.Function('w')(r); hs = sp.Function('h')(r)
Es = 1 + ws**2
def rN_gen(zz):
    kk = sp.diff(zz, r); pp = sp.diff(zz, th)/r
    DD = Es*(1-pp**2) - kk**2; QQ = kk + Es*sp.diff(pp, th)
    return (QQ*sp.diff(kk, r) - Es*r*sp.diff(pp, r)**2 - sp.diff(Es, r)/2*(1 - pp**2 + kk*sp.diff(pp, th)))/DD**sp.Rational(3,2)
lin0 = sp.diff(rN_gen(hs + eps*u), eps).subs(eps, 0).subs(sp.Derivative(hs, r), ws).doit()
lin0 = lin0.subs(sp.Derivative(hs, (r, 2)), sp.diff(ws, r)).subs(sp.Derivative(hs, r), ws)
target = sp.diff(ws*sp.diff(u, r), r) + sp.diff(ws, r)/r*sp.diff(u, th, 2)
print(f"{'PASS' if sp.simplify(lin0 - target)==0 else 'FAIL'}  linearization at z=h is (w u_r)_r + (w'/r) u_thth  (symbolic)")
ok &= sp.simplify(lin0 - target) == 0

# ---- marker curvature (Lemma 2.4)
x, y, A, Bm, kk, rho = sp.symbols('x y A B k rho', positive=True)
xi = A*x**2 + Bm*y**2; Xi = xi/(rho**2 - xi)
ux, uy = -kk*A*x*sp.exp(-Xi), -kk*Bm*y*sp.exp(-Xi)
Kmark = (sp.diff(ux, x)*sp.diff(uy, y) - sp.diff(ux, y)**2)/(1 + ux**2 + uy**2)**2
Xip = rho**2/(rho**2 - xi)**2
form = A*Bm*kk**2*sp.exp(-2*Xi)*(1 - 2*xi*Xip)/(1 + kk**2*sp.exp(-2*Xi)*(A**2*x**2 + Bm**2*y**2))**2
val = max(abs(float((Kmark - form).subs({x:.1*i, y:.07*j, A:1.3, Bm:.6, kk:2.5, rho:1.1}))) for i in range(4) for j in range(4))
report("marker curvature formula (7)", val)
print(f"{'PASS' if sp.simplify(sp.diff(ux, y) - sp.diff(uy, x))==0 else 'FAIL'}  marker: (u_x,u_y) is a gradient")

# ---- Appendix A
z_, zx, zy, zxx, zxy, zyy = sp.symbols('z z_x z_y z_xx z_xy z_yy', real=True)
vx, vy = 2*z_*zx, 2*z_*zy
vxx, vxy, vyy = 2*zx**2 + 2*z_*zxx, 2*zx*zy + 2*z_*zxy, 2*zy**2 + 2*z_*zyy
lhs = 2*z_**2*(vxx*vyy - vxy**2) - (vyy*vx**2 - 2*vxy*vx*vy + vxx*vy**2)
print(f"{'PASS' if sp.expand(lhs - 8*z_**4*(zxx*zyy - zxy**2))==0 else 'FAIL'}  App. A: 2v det Hess v - cof(Hess v)[dv,dv] = 8 z^4 det Hess z")
J = sp.symbols('J', positive=True); bf = sp.Function('b')(r); Ef = sp.Function('E')(r)
v = bf*sp.exp(sp.I*J*th)
Aa = sp.diff(v, r, 2) - sp.diff(Ef, r)/(2*Ef)*sp.diff(v, r)
Bb = sp.diff(v, r, th) - sp.diff(v, th)/r
Cc = sp.diff(v, th, 2) + r/Ef*sp.diff(v, r)
Kf = sp.diff(Ef, r)/(2*r*Ef**2)
dv2 = sp.diff(v, r)**2/Ef + sp.diff(v, th)**2/r**2
cubic = (2*v*(Aa*Cc - Bb**2) - (Cc*sp.diff(v, r)**2 - 2*Bb*sp.diff(v, r)*sp.diff(v, th) + Aa*sp.diff(v, th)**2)
         + 2*Kf*v*dv2*Ef*r**2)            # cubic part of (LHS - RHS) * E r^2
cubic = sp.simplify(cubic*sp.exp(-3*sp.I*J*th)*Ef/r)
aa = Ef*J**2/r; dd = sp.diff(Ef, r)*J**2/(2*r); b1, b2 = sp.diff(bf, r), sp.diff(bf, r, 2)
claimed = (2*bf*b1 - aa*bf**2)*b2 - b1**3 + aa*bf*b1**2 - 2*aa/r*bf**2*b1 + 2*aa/r**2*bf**3 + dd*bf**2*b1 - 2*dd/r*bf**3
print(f"{'PASS' if sp.simplify(cubic - claimed)==0 else 'FAIL'}  App. A: equation for the highest coefficient")
ok &= sp.simplify(cubic - claimed) == 0
yf = sp.Function('y')(r)
sub = claimed.subs(bf, yf**2).doit()
sq = 2*yf**4*((4*sp.diff(yf, r) - aa*yf)*sp.diff(yf, r, 2) + aa*(sp.diff(yf, r) - yf/r)**2 + dd*(yf*sp.diff(yf, r) - yf**2/r))
print(f"{'PASS' if sp.simplify(sub - sq)==0 else 'FAIL'}  App. A: square-root equation")
ok &= sp.simplify(sub - sq) == 0
print("\nALL PART I CHECKS PASSED" if ok else "\nSOME CHECK FAILED")
