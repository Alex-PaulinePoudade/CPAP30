# Info:
#  CPAP30 v1.9
#  Continuous CPAP-29/30 prime sequence 1st order PG-P search
#  Synopsys : pypy CPAP30.py
#  GNU3 2020-2021 Alex-Pauline Poudade (AlexPauline.Poudade@free.fr)
#  Platform : WINXP python 2.7.10, PyPy 5.4.1 with MSC v.1500 32-bit
#
# References:
#  ORCiD: https://orcid.org/0000-0003-3037-1091
#  DOI: https://doi.org/10.7910/DVN/W8RRMA
#  viXra: http://vixra.org/abs/2008.0154
#
# Revision history:
#  v1.0 21/06/2020 initial code
#  v1.1 22/06/2020 program reprisal management code
#  v1.3 23/06/2020 logging
#  v1.4 28/06/2020 maxval saving and debugging
#  v1.5 08/07/2020 code rewrite for first order only
#  v1.6 09/07/2020 added deterministic APR-CL primality tester (credit @wacchoz)
#  v1.7 10/07/2020 added Rosser-Schoenfeld theorem 3 corollary Pn>=nlogn (theorem of primes)
#  v1.8 11/07/2020 several code optimisitions and distributed array implementation
#  v1.9 11/07/2020 relative filePaths and distributed array devising
#
# Benchmark :
#  ~50000 to 120000 polynomials per second per shell on WIN7SP1 Intel Core i3 M 390 @ 2.67GHz (including display slowdown) 
#
# Sample output:
#  CPU:01 DOI:00000000000032228182 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00600" CPAP-PG-P(x=00)=000000001*P29#*x+0000000000001172933
#  CPU:01 DOI:00000000000032228183 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00900" CPAP-PG-P(x=01)=000000001*P29#*x+0000000000001172933
#  CPU:01 DOI:00000000000032228184 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00800" CPAP-PG-P(x=02)=000000001*P29#*x+0000000000001172933
#  CPU:01 DOI:00000000000032228185 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00800" CPAP-PG-P(x=03)=000000001*P29#*x+0000000000001172933
#  CPU:01 DOI:00000000000032228637 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00200" CPAP-PG-P(x=00)=000000001*P29#*x+0000000000001172953
#  CPU:01 DOI:00000000000032228728 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00200" CPAP-PG-P(x=00)=000000001*P29#*x+0000000000001172957
#  CPU:01 DOI:00000000000032229274 PPS:084123 CPAP-10:0000000006469693230x+0000000000000640943 APR:0.00200" CPAP-PG-P(x=00)=000000001*P29#*x+0000000000001172981
#
#  with a 3 (old) computers each running 4 virtual machines (array of 12), one can expect over a million of polynomials processed per second
#
# Distributed array:
#  modify cpu_max=<nb of computers/virtual machines> in configuration file
#   example with 3 computers/virtual machines to cover each 1/3 of P29 space:
#    on CPAP30.cfg of 1st computer set
#     [reprisal] 
#     cpuid = 1
#     cpu_max = 3
#    on CPAP30.cfg of 2nd computer set
#     [reprisal]
#     cpuid = 2
#     cpu_max = 3
#    on CPAP30.cfg of 3rd computer set
#     [reprisal]
#     cpuid = 3
#     cpu_max = 3
#
# Acronyms:
#  P=b*x^1+a*x^0
#  P-GP: Prime-Generating Polynomial
#  P-GP-n: Prime-Generating Polynomial of order n
#  OEIS: On-Line Encyclopedia of Integer Sequences
#  CPAP: Consecutive Primes in Arithmetic Progression
#  CPAP-n: Consecutive Primes in Arithmetic Progression of n-multiplet 
#  APR-CL: Adleman–Pomerance–Rumely-Cohen-Lenstra  cf. Lenstrahttps://en.wikipedia.org/wiki/Adleman%E2%80%93Pomerance%E2%80%93Rumely_primality_test
#  PPS: tested Polynomials per second
#
# Prequisites:
#  python 3.6.0+ (might work wirh previous vers)
#  note CPAP30.cfg and CPAP30.log must be present in same directory of cpap30.py
#  CPAP30.cfg default file:
# ---8<---------------------
# [DEFAULT]
# alwaysreprisal = 'true'
# [reprisal]
# cpuid = 1
# cpu_max = 3
# xrangemax = 30
# acoeffmax = 9999999999999999999
# bcoeffmax = 999999999
# a = 1
# b = 1
# a_max = 0
# b_max = 0
# testnumber = 0
# primeseqlen = 0
# polyprimeseqmax = 0
# degprimeseqmax = 0
# degprimeseqbeg = 0
# ---8<---------------------

import copy
import time
from math import log  # version >= 3.5
from fractions import gcd
#import random
import logging
import ConfigParser
#import sys


t_list = [
        2,
        12,
        60,
        180,
        840,
        1260,
        1680,
        2520,
        5040,
        15120,
        55440,
        110880,
        720720,
        1441440,
        4324320,
        24504480,
        73513440
        ]



# primality test by trial division
def isprime_slow(n):
    if n<2:
        return False
    elif n==2 or n==3:
        return True
    elif n%2==0:
        return False
    else:
        i = 3
        while i*i <= n:
            if n%i == 0:
                return False
            i+=2
    return True        


# v_q(t): how many time is t divided by q
def v(q, t):
    ans = 0
    while(t % q == 0):
        ans +=1
        t//= q
    return ans


def prime_factorize(n):
    ret = []
    p=2
    while p*p <= n:
        if n%p==0:
            num = 0
            while n%p==0:
                num+=1
                n//= p
            ret.append((p,num))
        p+= 1

    if n!=1:
        ret.append((n,1))

    return ret


# calculate e(t)
def e(t):
    s = 1
    q_list = []
    for q in range(2, t+2):
        if t % (q-1) == 0 and isprime_slow(q):
            s *= q ** (1+v(q,t))
            q_list.append(q)
    return 2*s, q_list

# Jacobi sum
class JacobiSum(object):
    def __init__(self, p, k, q):
        self.p = p
        self.k = k
        self.q = q
        self.m = (p-1)*p**(k-1)
        self.pk = p**k
        self.coef = [0]*self.m

    # 1
    def one(self):
        self.coef[0] = 1
        for i in range(1,self.m):
            self.coef[i] = 0
        return self


    # product of JacobiSum
    # jac : JacobiSum
    def mul(self, jac):
        m = self.m
        pk = self.pk
        j_ret=JacobiSum(self.p, self.k, self.q)
        for i in range(m):
            for j in range(m):
                if (i+j)% pk < m:
                    j_ret.coef[(i+j)% pk] += self.coef[i] * jac.coef[j]
                else:
                    r = (i+j) % pk - self.p ** (self.k-1)                    
                    while r>=0:
                        j_ret.coef[r] -= self.coef[i] * jac.coef[j]
                        r-= self.p ** (self.k-1)

        return j_ret


    def __mul__(self, right):
        if type(right) is int:
            # product with integer
            j_ret=JacobiSum(self.p, self.k, self.q)
            for i in range(self.m):
                j_ret.coef[i] = self.coef[i] * right
            return j_ret
        else:
            # product with JacobiSum
            return self.mul(right)
    

    # power of JacobiSum（x-th power mod n）
    def modpow(self, x, n):
        j_ret=JacobiSum(self.p, self.k, self.q)
        j_ret.coef[0]=1
        j_a = copy.deepcopy(self)
        while x>0:
            if x%2==1:
                j_ret = (j_ret * j_a).mod(n)
            j_a = j_a*j_a
            j_a.mod(n)
            x //= 2
        return j_ret
    

    # applying "mod n" to coefficient of self
    def mod(self, n):
        for i in range(self.m):
            self.coef[i] %= n
        return self
    

    # operate sigma_x
    # verification for sigma_inv
    def sigma(self, x):
        m = self.m
        pk = self.pk
        j_ret=JacobiSum(self.p, self.k, self.q)
        for i in range(m):
            if (i*x) % pk < m:
                j_ret.coef[(i*x) % pk] += self.coef[i]
            else:
                r = (i*x) % pk - self.p ** (self.k-1)                    
                while r>=0:
                    j_ret.coef[r] -= self.coef[i]
                    r-= self.p ** (self.k-1)
        return j_ret
    
                
    # operate sigma_x^(-1)
    def sigma_inv(self, x):
        m = self.m
        pk = self.pk
        j_ret=JacobiSum(self.p, self.k, self.q)
        for i in range(pk):
            if i<m:
                if (i*x)%pk < m:
                    j_ret.coef[i] += self.coef[(i*x)%pk]
            else:
                r = i - self.p ** (self.k-1)
                while r>=0:
                    if (i*x)%pk < m:
                        j_ret.coef[r] -= self.coef[(i*x)%pk]
                    r-= self.p ** (self.k-1)

        return j_ret
    

    # Is self p^k-th root of unity (mod N)
    # if so, return h where self is zeta^h
    def is_root_of_unity(self, N):
        m = self.m
        p = self.p
        k = self.k

        # case of zeta^h (h<m)
        one = 0
        for i in range(m):
            if self.coef[i]==1:
                one += 1
                h = i
            elif self.coef[i] == 0:
                continue
            elif (self.coef[i] - (-1)) %N != 0:
                return False, None
        if one == 1:
            return True, h

        # case of zeta^h (h>=m)
        for i in range(m):
            if self.coef[i]!=0:
                break
        r = i % (p**(k-1))
        for i in range(m):
            if i % (p**(k-1)) == r:
                if (self.coef[i] - (-1))%N != 0:
                    return False, None
            else:
                if self.coef[i] !=0:
                    return False, None

        return True, (p-1)*p**(k-1)+ r
         
# sum zeta^(a*x+b*f(x))
def calc_J_ab(p, k, q, a, b):
    j_ret = JacobiSum(p,k,q)
    g = None ; #  calculate f_q(x)  f = calc_f(q) find primitive root smallest_primitive_root(q)
    for r in range(2, q):
        s = set({})
        m = 1
        for i in range(1, q):
            m = (m*r) % q
            s.add(m)
        if len(s) == q-1:
            g = r
    m = {}
    for x in range(1,q-1):
        m[pow(g,x,q)] = x
    f = {}
    for x in range(1,q-1):
        f[x] = m[ (1-pow(g,x,q))%q ]
    for x in range(1,q-1):
        pk = p**k
        if (a*x+b*f[x]) % pk < j_ret.m:
            j_ret.coef[(a*x+b*f[x]) % pk] += 1
        else:
            r = (a*x+b*f[x]) % pk - p**(k-1)
            while r>=0:
                j_ret.coef[r] -= 1
                r-= p**(k-1)
    return j_ret

# Step 4
def APRtest_step4(p, k, q, N):
    if p>=3: #APRtest_step4a(p, k, q, N)
        J = calc_J_ab(p, k, q, 1, 1)
        # initialize s1=1
        s1 = JacobiSum(p,k,q).one()
        # J^Theta
        for x in range(p**k):
            if x % p == 0:
                continue
            t = J.sigma_inv(x)
            t = t.modpow(x, N)
            s1 = s1 * t
            s1.mod(N)
        # r = N mod p^k
        r = N % (p**k)
        # s2 = s1 ^ (N/p^k)
        s2 = s1.modpow(N//(p**k), N)
        # J^alpha
        J_alpha = JacobiSum(p,k,q).one()
        for x in range(p**k):
            if x % p == 0:
                continue
            t = J.sigma_inv(x)
            t = t.modpow((r*x)//(p**k), N)
            J_alpha = J_alpha * t
            J_alpha.mod(N)
        # S = s2 * J_alpha
        S = (s2 * J_alpha).mod(N)
        # Is S root of unity
        exist, h = S.is_root_of_unity(N)
        if not exist:
            # composite!
            result=False
            l_p=None
        else:
            # possible prime
            if h%p!=0:
                l_p = 1
            else:
                l_p = 0
            result=True
    elif p==2 and k>=3: # APRtest_step4b(p, k, q, N)
        j2q = calc_J_ab(p, k, q, 1, 1) # def calc_J3(p, k, q):calculate J_3(q)（p=2 and k>=3）
        j21 = calc_J_ab(p, k, q, 2, 1)
        J = j2q * j21 # J = calc_J3(p, k, q)
        # initialize s1=1
        s1 = JacobiSum(p,k,q).one()
        # J3^Theta
        for x in range(p**k):
            if x % 8 not in [1,3]:
                continue
            t = J.sigma_inv(x)
            t = t.modpow(x, N)
            s1 = s1 * t
            s1.mod(N)
        # r = N mod p^k
        r = N % (p**k)
        # s2 = s1 ^ (N/p^k)
        s2 = s1.modpow(N//(p**k), N)
        # J3^alpha
        J_alpha = JacobiSum(p,k,q).one()
        for x in range(p**k):
            if x % 8 not in [1,3]:
                continue
            t = J.sigma_inv(x)
            t = t.modpow((r*x)//(p**k), N)
            J_alpha = J_alpha * t
            J_alpha.mod(N)
        # S = s2 * J_alpha * J2^delta
        if N%8 in [1,3]:
            S = (s2 * J_alpha ).mod(N)
        else:
            j31 = calc_J_ab(2, 3, q, 3, 1) # def calc_J2(p, k, q): calculate J_2(q)（p=2 and k>=3）
            j_conv = JacobiSum(p, k, q)
            for i in range(j31.m):
                j_conv.coef[i*(p**k)//8] = j31.coef[i]
            J2_delta = j_conv * j_conv   
            S = (s2 * J_alpha * J2_delta).mod(N)
        # Is S root of unity
        exist, h = S.is_root_of_unity(N)
        if not exist:
            # composite 
            result=False
        else:
            # possible prime
            if h%p!=0 and (pow(q,(N-1)//2,N) + 1)%N==0:
                l_p = 1
            else:
                l_p = 0
            result=True
    elif p==2 and k==2: # APRtest_step4c(p, k, q, N)
        J2q = calc_J_ab(p, k, q, 1, 1)
        # s1 = J(2,q)^2 * q (mod N)
        s1 = (J2q * J2q * q).mod(N)
        # s2 = s1 ^ (N/4)
        s2 = s1.modpow(N//4, N)
        if N%4 == 1:
            S = s2
        elif N%4 == 3:
            S = (s2 * J2q * J2q).mod(N)
        else:
            print("Error")
        # Is S root of unity
        exist, h = S.is_root_of_unity(N)
        if not exist:
            # composite
            result=False
            l_p=None
        else:
            # possible prime
            if h%p!=0 and (pow(q,(N-1)//2,N) + 1)%N==0:
                l_p = 1
            else:
                l_p = 0
            result=True
    elif p==2 and k==1: #APRtest_step4d(p, k, q, N)
        S2q = pow(-q, (N-1)//2, N)
        if (S2q-1)%N != 0 and (S2q+1)%N != 0:
            # composite
            result=False
            l_p=None
        else:
            # possible prime
            if (S2q + 1)%N == 0 and (N-1)%4==0:
                l_p=1
            else:
                l_p=0
            result=True
    else:
        print("error")
    if not result:
     return False, None
    return result, l_p


def APRtest(N):

    if N<=3:
        return False
    # Select t
    for t in t_list:
        et, q_list = e(t)
        if N < et*et:
            break
    else:
        return False
    # Step 1
    g = gcd(t*et, N)
    if g > 1:
        return False
    # Step 2
    l = {}
    fac_t = prime_factorize(t)
    for p, k in fac_t:
        if p>=3 and pow(N, p-1, p*p)!=1:
            l[p] = 1
        else:
            l[p] = 0
    # Step 3 & Step 4
    for q in q_list:
        if q == 2:
            continue
        fac = prime_factorize(q-1)
        for p,k in fac:
            # Step 4
            result, l_p = APRtest_step4(p, k, q, N)
            if not result:
                # composite
                return False
            elif l_p==1:
                l[p] = 1
    # Step 5          
    for p, value in l.items():
        if value==0:
            # try other pair of (p,q)
            count = 0
            i = 1
            found = False
            # try maximum 30 times
            while count < 30:
                q = p*i+1
                if N%q != 0 and isprime_slow(q) and (q not in q_list):
                    count += 1
                    k = v(p, q-1)
                    # Step 4
                    result, l_p = APRtest_step4(p, k, q, N)
                    if not result:
                        # composite
                        return False
                    elif l_p == 1:
                        found = True
                        break
                i += 1
            if not found:
                return False
    # Step 6
    r = 1
    for t in range(t-1):
        r = (r*N) % et
        if r!=1 and r!= N and N % r == 0:
            return False
    # prime!!
    return True


#if __name__ == '__main__':


#    start_time = time.time()
#    if APRtest(224584605939537911)==True:
#     print("Prime!")
#    else:
#     print("composite")
#    APRtest(24354354334)
#    APRtest(2**521-1)   # 157 digit, 18 sec
#    APRtest(2**1279-1)  # 386 digit, 355 sec
#    APRtest(2074722246773485207821695222107608587480996474721117292752992589912196684750549658310084416732550077)

#    end_time = time.time()
#    print(end_time - start_time, "sec")


# read program reprisal external config parameters
prime_config=ConfigParser.ConfigParser()
prime_config.read('.\CPAP30.cfg') # CHANGE your PATH
cpuid=int(prime_config.get('reprisal','cpuid'))
cpu_max=int(prime_config.get('reprisal','cpu_max'))
xrangemax=int(prime_config.get('reprisal','xrangemax'))
acoeffmax=int(prime_config.get('reprisal','acoeffmax'))
bcoeffmax=int(prime_config.get('reprisal','bcoeffmax'))
a=int(prime_config.get('reprisal','a'))
b=int(prime_config.get('reprisal','b'))
a_max=int(prime_config.get('reprisal','a_max'))
b_max=int(prime_config.get('reprisal','b_max'))
testNumber=int(prime_config.get('reprisal','testNumber'))
primeSeqLen=int(prime_config.get('reprisal','primeSeqLen'))
polyPrimeSeqMax=int(prime_config.get('reprisal','polyPrimeSeqMax'))
degPrimeSeqMax=int(prime_config.get('reprisal','degPrimeSeqMax'))
degPrimeSeqBeg=int(prime_config.get('reprisal','degPrimeSeqBeg'))
logging.basicConfig(filename='.\CPAP30.log',level=logging.INFO)



###### global vars initialisation
Pn=1 # adjust for APR undetected prime number 3
P29=6469693230 # P29 isPrimorial 29 cf. Green-Tao and Tao-Ziegler theorems applied to CPAP-30 search
primeSeqBeg=0
totalNumber=0
start_number=0
end_number=0
totalTime=0
APRstart_time=0
reprisal=0
start_b=(cpuid-1)*int(bcoeffmax/cpu_max)
bP29=(start_b+b)*P29
bP29_max=b_max*P29
testNumberStart=(cpuid-1)*int(((bcoeffmax*xrangemax+acoeffmax)/cpu_max)) # xrangemax = 30 acoeffmax = 9999999999999999999 bcoeffmax = 999999999 999999999*30+9999999999999999999=10000000029999999969


while True : 
 start_time = time.time()
##########################################################
 primeSeqLen=0 # new polynomial coefficients reset any prime sequence length
 polyPrimeSeqMax=0
 for x in range (0,xrangemax) :
  testNumber=testNumber+1
  candidate=bP29*x+a
  APRstart_time = time.time()
  if APRtest(candidate)==True : # APR-CL deterministic PRP
   primeSeqBeg=x-primeSeqLen #testNumber   
   Pn+=1 # increase total number of primes
   primeSeqLen+=1
   if primeSeqLen>polyPrimeSeqMax:
    polyPrimeSeqMax=primeSeqLen
    if polyPrimeSeqMax>degPrimeSeqMax:
     degPrimeSeqMax=polyPrimeSeqMax    
     degPrimeSeqBeg=primeSeqBeg
     a_max=a
     b_max=b
     bP29_max=b_max*P29
     logging.info("CPU:%s DOI:%s PPS:%s CPAP-%s:%sx+%s APR:%s\" CPAP-PG-P(x=%s)=%s*P29#*x+%s",str(cpuid).zfill(2),str(testNumberStart+testNumber).zfill(20),str(totalNumber).zfill(6),str(degPrimeSeqMax).zfill(2),str(bP29).zfill(19),str(a_max).zfill(19),'{:01.5f}'.format(time.time() - APRstart_time),str(x).zfill(2),str(start_b+b).zfill(9),str(a).zfill(19))
   APRend_time = time.time()

   #print("CPU:",str(cpuid).zfill(2)," DOI:",str(testNumberStart+testNumber).zfill(20)," PPS:",str(totalNumber).zfill(6)," CPAP-",str(degPrimeSeqMax).zfill(2),":",str(bP29).zfill(19),"x+",str(a_max).zfill(19)," APR:",'{:01.5f}'.format(APRend_time - APRstart_time), "\" CPAP-PG-P(x=",str(x).zfill(2),")=",str(start_b+b).zfill(9),"*P29#*x+",str(a).zfill(19))
   print'CPU:{} DOI:{} PPS:{} CPAP-{}:{}x+{} APR:{}" CPAP-PG-P(x={})={}*P29#*x+{}'.format(str(cpuid).zfill(2),str(testNumberStart+testNumber).zfill(20),str(totalNumber).zfill(6),str(degPrimeSeqMax).zfill(2),str(bP29).zfill(19),str(a_max).zfill(19),'{:01.5f}'.format(time.time() - APRstart_time),str(x).zfill(2),str(start_b+b).zfill(9),str(a).zfill(19))

  else :
   #print(candidate, " not prime aborting xrange")
   # primeSeqLen=0
   testNumber+=xrangemax-x # total polynomials dropped because of discontinuity 
   break   

 if a<acoeffmax : #degree 0  
  a+=2 # skip even numbers
  testNumber+=xrangemax
  # won't enter block at least once even if False contrary to C
  while(a<Pn*log(Pn)): # Rosser-Schoenfeld theorem 3 corollary: n*log(n) <= P(n) n>=1 where n=nth Prime
   a+=2 # skip even numbers
   testNumber+=xrangemax # skipping whole for loop for x range since P(x=0) ought to be prime by P(x=0)<P(Pn)*log(P(Pn))  
   #print("skipping non Rosser-Schoenfeld compliant candidate")  
   break # non Rosser-Schoenfeld compliant needs no testing  
 else :
  a=1
  if b<bcoeffmax :
   b+=1
   bP29+=P29

 # calculate PPS: tested polynmials per second
 end_time = time.time()
 totalTime=totalTime+end_time-start_time 
 if totalTime>1.0:
  totalTime-=1.0
  start_number=end_number
  end_number=testNumber
  totalNumber=end_number-start_number
  reprisal+=1
  if reprisal>4095: # save snapshot every 1h8'16" (2^12 bitmask)
   reprisal=0
   # write program reprisal external config parameters
   prime_config.set('reprisal','cpuid','%(cpuid)s')
   prime_config.set('reprisal','cpu_max','%(cpu_max)s')
   prime_config.set('reprisal','xrangemax','%(xrangemax)s')
   prime_config.set('reprisal','acoeffmax','%(acoeffmax)s')
   prime_config.set('reprisal','bcoeffmax','%(bcoeffmax)s')
   prime_config.set('reprisal','a','%(a)s')
   prime_config.set('reprisal','b','%(b)s')
   prime_config.set('reprisal','a_max','%(a_max)s')
   prime_config.set('reprisal','b_max','%(b_max)s')
   prime_config.set('reprisal','testNumber','%(testNumber)s')
   prime_config.set('reprisal','primeSeqLen','%(primeSeqLen)s')
   prime_config.set('reprisal','polyPrimeSeqMax','%(polyPrimeSeqMax)s')
   prime_config.set('reprisal','degPrimeSeqMax','%(degPrimeSeqMax)s')
   prime_config.set('reprisal','degPrimeSeqBeg','%(degPrimeSeqBeg)s')
   with open('CPAP30.cfg', 'w') as configfile:
    prime_config.write(configfile)
 
