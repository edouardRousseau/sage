r"""
Experimental file for discrete logarithm.

"""

#*****************************************************************************
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.ext.sage_object import SageObject

class smsrField(SageObject):
    """
    Class created to gather informations about the
    sparse medium subfield representation (smsr).
    """
    
    def __init__(self, q, k):
        self._characteristic = q
        self._extensionDegree = k
        self._mediumSubField = GF(q^2, "x")
        
        b = True
        FT.<T> = PolynomialRing(self.medium_subfield(),"T")
        
        while b:
            h0, h1 = FT.random_element(), FT.random_element(degree = 1) + T^2
            for f in factor(h1*T^q - h0):
                if (f[0].degree() == k):
                    b = False
                    self._definingPolynomial = f[0]
                    self._h0 = h0
                    self._h1 = h1
                    break
        
        self._bigField = self.medium_subfield().extension(self.defining_polynomial())
        
        self._gen = self.field().random_element()
        if (self.cardinality() - 1 < 10^50):
            boo = True
            fact = factor(self.cardinality() - 1) # not polynomial, hard
            while boo:
                boo = False
                for f in fact:
                    exp = (self.cardinality() - 1)/f[0]
                    if (self._gen^exp).is_one():
                        boo = True
                        break
                if boo:
                    self._gen = self.field().random_element()
                    
    def medium_subfield(self):
        return self._mediumSubField
    
    def characteristic(self):
        return self._characteristic
    
    def extension_degree(self):
        return self._extensionDegree
    
    def h0(self):
        return self._h0
    
    def h1(self):
        return self._h1
    
    def defining_polynomial(self):
        return self._definingPolynomial
    
    def cardinality(self):
        return self.characteristic()^(2*self.extension_degree())
    
    def field(self):
        return self._bigField

    def gen(self):
        return self._gen

class factorsList(SageObject):
    
    def __init__(self, P):
        self._factors = [P]
        self._coefs = [1]
        self._unit = 1
    
    def __repr__(self):
        return str(self.list())
        
    def len(self):
        return len(self._factors)
    
    def list(self):
        return [(self._factors[i], self._coefs[i]) for i in range(len(self._factors))]

    def __getitem__(self, i):
        return (self._factors[i], self._coefs[i])
    
    def append(self, factor, coef):
        try:
            i = self._factors.index(factor)
            self._coefs[i] = self._coefs[i] + coef
        except(ValueError):
            self._factors.append(factor)
            self._coefs.append(coef)
    
    def simplify(self):
        i = 0
        while (i < self.len()):
            if (self._coefs[i] == 0):
                self._coefs.pop(i)
                self._factors.pop(i)
            else:
                i = i + 1
    
    def remove(self, i):
        self._factors.pop(i)
        self._coefs.pop(i)
    
    def unit(self):
        return self._unit
    
    def multiply_unit(self, coef):
        self._unit = self._unit*coef

def dlsf(elem, K):
    """
    dlsf stands for discrete logarithm in the small field
    
    Compute the discrete logarithm of elem in the basis gen.
    
    INPUT::
        elem : element of `F_{q^2}^*`
        gen : generator of `F_{q^(2k)}^*`
    """
    
    qq = K.characteristic()^2
    k = K.extension_degree()
    gen = K.gen()
    
    c = (qq^k - 1)/(qq - 1)
    n = gen^c # n = gen.norm()
    
    i = 1
    while (n^i != elem):
        i = i + 1
    
    return i*c

def P1(F):
    l = list()
    for f in F:
        l.append((f,F(1)))
    l.append((F(-1), F(0)))
    return l

def isSmooth(P, D):
    
    d = ceil(D/2)
    
    for f in factor(P):
        if (f[0].degree() > d):
            return False
    
    return True

def pgl2(F):
    
    M, N = Matrix(F, 2), Matrix(F, 2)
    L = list()
    M[0,0] = F(1)
    N[0,0], N[0, 1] = 0, 1
    
    for a in F:
        for b in F:
            for c in F:
                if not (c - a*b == 0):
                    M[0,1], M[1,0], M[1,1] = a, b, c
                    L.append(copy(M))
            
            if not (a == 0):
                N[1,0], N[1,1] = a, b
                L.append(copy(N))
                
    return L

def isConjugate(A, B, K):
    M = B^(-1)*A
    a = M[0, 0]
    q = K.characteristic()
    Fq = GF(q)
    if (a != 0):
        b = M[0,1]/a
        c = M[1, 0]/a
        d = M[1, 1]/a
        if ((d-b*c != 0) and (b in Fq) and (c in Fq) and (d in Fq)):
            return True
        else:
            a = M[0,1]
            if (a != 0):
                b = M[1, 0]/a
                c = M[1, 1]/a
                if ((b != 0) and (b in Fq) and (c in Fq)):
                    return True
    return False

def constructPq(K):
    L = list()
    PGL = pgl2(K.medium_subfield())
    q = K.characteristic()
    for i in range(len(PGL)):
        if (len(L) == q^3 + q):
            break
        else:
            boo = True
            for j in range(len(L)):
                if isConjugate(PGL[i], L[j], K):
                    boo = False
                    break
    
            if boo:
                L.append(PGL[i])
    return L

def descent(L, i0, K):
    """
    The descent corresponding to the BGJT algorithm.
    
    INPUT::
        P : element of F_q²[T] (a polynomial !), in order to
        have the functions factors, degree, subs that do not
        exist in the quotient ring.
    """
    P = L[i0][0]
    coef = L[i0][1]
    D = P.degree()
    S = list()
    F = K.medium_subfield()
    q = K.characteristic()
    M = Matrix(ZZ, q^3+q, q^2+1)
    lambdas = list()
    Fq = GF(q)
    P1Fq = P1(Fq)
    P1Fq2 = P1(F)
    j = 0
    Pq = constructPq(K)
    
    for m in Pq:
        a, b, c, d = m[0,0], m[0,1], m[1,0], m[1,1]
        Ptilde = P.parent()([coef^q for coef in P])

        J = ( a^q * Ptilde.subs(K.h0()/K.h1()) + b^q )(c*P + d) - (a*P + b)*(c^q * Ptilde.subs(K.h0()/K.h1()) + d^q )
        # ã = a^q, ~b = b^q, ~P is P with all coefficients power q

        N = K.h1()^D*J

        if isSmooth(N, D): # We have to find the factors of N_m here
            unit = 1
            for i in range(q^2+1):
                alpha = a*P1Fq2[i][0] + b*P1Fq2[i][1]
                beta = c*P1Fq2[i][0] + d*P1Fq2[i][1]
                
                if (beta != 0):
                    if (alpha/beta in Fq):
                        M[j, i] = 1
                else:
                    M[j, i] = 1
                
                tmp = -c*P1Fq2[i][0] + a*P1Fq2[i][1]
                
                if (tmp != 0):
                    unit = unit*tmp
                else:
                    unit = unit*(-d*P1Fq2[i][0] + b*P1Fq2[i][1])
            
            lambdas.append(unit^(-1))
            
            j = j + 1
            S.append(N)

    # We assume (heuristic) that M has full rank

    z = MatrixSpace(ZZ, 1, q^2+1)()
    z[0,0] = 1
#    print(M.str())
    sol = M.solve_left(z)
    
    for i in range(q^3 + q):
        if (sol[i] != 0):
            fact = factor(S[i])
            for (f,e) in fact:
                L.append(f, e*sol[i]*coef) 
                L.append(K.h1(), D*sol[i]*coef) 
                L.remove(i0)
                
            L.modify_unit((fact.unit()*lambdas[i])^(sol[i]*coef))

def linearDict(Log, K):
    """
    Compute the discrete logarithm of the form X + a where
    a is in the medium subfield.
    """
    F = K.medium_subfield()
    q = K.characteristic()
    M = Matrix(Zmod(K.cardinality() - 1), q^3+q, q^2+2) # +2 because of h1
    lambdas = list()
    Fq = GF(q)
    P1Fq = P1(Fq)
    P1Fq2 = P1(F)
    j = 0
    X = parent(K.h0()).gen()
    Pq = constructPq(K)
    
    for m in Pq:
        a, b, c, d = m[0,0], m[0,1], m[1,0], m[1,1]

        J = ( a^q *(K.h0()/K.h1()) + b^q )(c*X + d) - (a*X + b)*(c^q *K.h0()/K.h1() + d^q )

        N = K.h1()*J

        if isSmooth(N, 1): # We have to find the factors of N_m here
            unit = 1
            for i in range(q^2+1):
                alpha = a*P1Fq2[i][0] + b*P1Fq2[i][1]
                beta = c*P1Fq2[i][0] + d*P1Fq2[i][1]
                
                if (beta != 0):
                    if (alpha/beta in Fq):
                        M[j, i] = 1
                else:
                    M[j, i] = 1
                
                tmp = -c*P1Fq2[i][0] + a*P1Fq2[i][i]
                
                if (tmp != 0):
                    unit = unit*tmp
                else:
                    unit = unit*(-d*P1Fq2[i][0] + b*P1Fq2[i][1])
            
            fact = factor(N)
            lambdas.append(fact.unit()*unit^(-1))
            for f, e in fact:
                i = P1Fq2.index((f[0],1))
                M[j, i] = M[j, i] - e
            
            M[j, q^2 + 1] = 1
            j = j + 1

    # We assume (heuristic) that M has full rank

    z = MatrixSpace(Zmod(K.cardinality() - 1), 1, q^2+2)()
    for i in range(q^2 + 2):
        z[0,i] = dlsf(lambdas[i], K)
    sol = M.solve_left(z)
    
    j = 0
    for s in sol:
        if (s != 0):
            if (j==q^2):
                Log[K.h1()] = s
                break
            Log[X + P1Fq2[j][0]] = s
            j += 1

def BGJT(P, K):
    i = 0
    L = factorsList(P)
    
    while (i < L.len()):
        while (L[i][0].degree() >= 2):
            descent(L, i, K)
        i =  i + 1
    
    # We now have only linear polynomials in L
    
    # We compute the logarithms of the linear polynomials
    Log = dict()
    linearDict(Log, K)
    
    return sum([L[i][1]*Log[L[i][0]] for i in range(L.len())]) + dlsf(L.unit(), K)
