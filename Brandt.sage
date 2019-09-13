########################################################################
## Description: A minimal class that computes the Brandt matrices 
##      for certain quaternionic norm forms.
##
## Written by Lassina Dembele and Jonathan Hanke while visiting the 
##	Max Planck Institute in Bonn, Germany in Fall 2007.
##
########################################################################

#*****************************************************************************
#       Copyright (C) 2007 Lassina Dembele and Jonathan Hanke
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

## TO DO LIST:
##
##     - Add a routine to compute a compatible system of eigenvalues!
##





from sage.modular.modsym.p1list import p1_normalize



def product_as_lists(list_of_lists):
    """
    Compute the list of lists L whose i-th component L[i] runs over
    all elements of the i-th list/tuple (given as the i-th component of
    list_of_lists.
    """
    ## Routine to compute the "Direct Product"
    Prod_list = []
    mrange_vec = [len(list_of_lists[i])  for i in range(len(list_of_lists))]
    for v in mrange(mrange_vec):
        Prod_list.append([list_of_lists[j][v[j]]  for j in range(len(list_of_lists))])
    return Prod_list


def product_as_tuples(list_of_lists):
    """
    Compute the list of tuples L whose i-th component L[i] runs over
    all elements of the i-th list/tuple (given as the i-th component of
    list_of_lists.
    """
    #def fix_tuple(L):
    #   if len(L)


    ## Routine to compute the "Direct Product"
    Prod_list = []
    mrange_vec = [len(list_of_lists[i])  for i in range(len(list_of_lists))]
    for v in mrange(mrange_vec):
        Prod_list.append(tuple([list_of_lists[j][v[j]]  for j in range(len(list_of_lists))]))
    return Prod_list






##############################################
## Class to compute in a quaternion algebra ##
## with level N, where (N,D) = 1.           ##
##############################################
#
# TO DO:
#    - Maximal order finding       <===  Right now this only works for the Hamiltonian quaternions.
#    - Class number finding
#
## ======================================================


def R_trace(x):
    return x + x.conjugate()


def R_norm(x):
    return x * x.conjugate()


## =============================



class QuaternionAlgebraWithLevelStructure(SageObject):      ## <<------ TODO: We really want QuaternionAlgebra_generic here!!!
    """
    Defines a quaternion algebra with level structure, which allows
    one to compute automorphic forms on it.
    """
    def __init__(self, Base_field, a, b, N):
        """
        Defines a quaternion algebra via the Hilbert symbol (a,b/.)
        with level N structure, where N is prime to the discriminant D
        of the quaternion algebra.
        """
        ## Sanity checks
        if not (N in ZZ and N > 0):
            raise TypeError, "Oops!  The level N must be a natural number."


        ## Basic Information
        self.__base_field = Base_field
        self.__H = QuaternionAlgebra(Base_field, a,b, "iii, jjj, kkk")
        #self.__H_gens == self.__H.gens()
        self.__N = N


        ## Level Factorization
        D = self.__H.discriminant()
        ff = factor(N)
        ff_prime_list = [ff[i][0] for i in range(len(ff))]
        self.__good_level_primes = [p  for p in ff_prime_list  if D % p != 0]
        self.__bad_level_primes = [p  for p in ff_prime_list  if D % p == 0]


        ## Splitting Information (at split primes)
        self.__store_quaternionic_level_splitting()    ## NOTE: This deliberately sets global variables internally!!!

        ## Integer Information
        self.__basis_for_maximal_order = self.basis_for_maximal_order()
        self.__pos_vector_list_of_small_length = self.__positive_vectors_of_small_length(10)
        #print "small[:5] = ", self.__pos_vector_list_of_small_length[:5]
        #print "small[1] = ", self.__pos_vector_list_of_small_length[1]
        half_of_units = [self.element_from_integral_basis_coordinates(v) \
                     for v in self.__pos_vector_list_of_small_length[1]]
        self.__half_of_units = half_of_units
        self.__units = half_of_units + [u*(-1) for u in half_of_units]

        ## Orbit Information (at all primes p|N)
        self.__prepare_hecke_action()    ## NOTE: This deliberately sets global variables internally!!!

        ## Brandt matrices for small primes
        self.__brandt_matrix_list_at_prime_powers = []


    def discriminant(self):
        """
        Returns the discriminant of the underlying quaternion algebra
        """
        return self.quaternion_algebra().discriminant()
    

    def quaternion_algebra(self):
        """
        Returns the underlying quaternion algebra H = H
        """
        return self.__H

    def one(self):
        """
        Returns the quaternion i.
        """
        return self.__H(1)

    def i(self):
        """
        Returns the quaternion i.
        """
        return self.__H.gens()[0]

    def j(self):
        """
        Returns the quaternion j.
        """
        return self.__H.gens()[1]

    def k(self):
        """
        Returns the quaternion k.
        """
        return self.__H.gens()[2]


    def base_field(self):
        """
        Returns the base field over which the quaternion algebra is defined.
        """
        return self.__base_field
    

    def level(self):
        """
        Returns the natural number N defining the level structure.
        """
        return self.__N
    

    def level_at_split_primes(self):
        """
        Returns the natural number N defining the level structure.
        """
        return prod([p**valuation(self.__N, p)  for p in self.good_level_primes()])


    def level_at_ramified_primes(self):
        """
        Returns the natural number N defining the level structure.
        """
        return prod([p**valuation(self.__N, p)  for p in self.bad_level_primes()])


    def level_splitting_vector(self):
        """
        Returns the vector of matrices defining the images of
        [1, i, j, k]  into M_2(Z/NZ).
        """
        return self.__basis_embedding_vector


    def good_level_primes(self):
        """
        List of primes dividing the level where the quaternion algebra is split.
        """
        return self.__good_level_primes

    def bad_level_primes(self):
        """
        List of primes dividing the level where the quaternion algebra is ramified.
        """
        return self.__bad_level_primes


    def _repr_(self):
        """
        Print the quaternion algebra with level stucture.
        """
        return str(self.quaternion_algebra()) + " of level " + str(self.level()) + " over " + str(self.base_field()) + "."
    

    def __call__(self, x):
        """
        Coerce an element into the quaternion algebra
        """
        return self.quaternion_algebra()(x)
    

    def basis_for_maximal_order(self):                                   ## <<---------- FIX THIS!!!
        """
        Returns an (ordered) basis for the maximal order of this
        quaternion algebra.

	NOTE: WE ASSUME THAT THE FIRST BASIS VECTOR HERE IS 1.
        """
	return self.quaternion_algebra().maximal_order().basis()

	## OLDER CODE -- TO REMOVE
        #if self.discriminant() == 2:  # For (-1, -1) only!
        #    #one = self.quaternion_algebra()(1)
        #    return [self.one(), self.i(), self.j(), (self.one() + self.i() + self.j() + self.k()) / 2]
        #elif self.discriminant() == 7: # For (-1, -7) only!
        #    return [self.one(), self.i(), (self.i() + self.k())/2, (self.one() + self.j()) / 2]
        #else:
        #    raise NotImplementedError, "Oops... we need to implement this in general.  Right now only D=2 works!"
#       #     return [0,0,0,0]


    def element_from_integral_basis_coordinates(self, coord_vec):
        """
        Returns an element given as a tuple of coefficients for the
        stored basis of the ring of integers.
        """
        R_basis = self.basis_for_maximal_order()
        return sum([coord_vec[i] * R_basis[i]  for i in range(4)])
    

    def units(self):
        """
        Returns a list of the units of H.
        """
        return self.__units

    def units_up_to_sign(self):
        """
        Returns a list of the units of H.
        """
        return self.__half_of_units


    def fundamental_domain(self):
        """
        Returns a list of the units of H.
        """
        return self.__fund_domain_list


    def in_same_orbit(self, Q1, Q2):
        """
        Determines if two points in P1(N) are in the same orbit.
        """
        return self.__lookup_table[self.__symmetric_space.index(Q1)] == self.__lookup_table[self.__symmetric_space.index(Q2)]


    def orbit_lookup_table(self):
        """
        Return the lookup table used to quickly determine the orbits
        of points. Specifically, orbit_lookup_table()[i] stores the
        index of the orbit of the element symmetric_space()[i].
        """
        return self.__lookup_table


    def symmetric_space(self):
        """
        Returns the list of elements in the symmetic space.
        """
        return self.__symmetric_space


    def orbit_representative(self, P):
        """
        Give the element in the fundamental domain of P^1(Z/NZ)
        equivalent to the point P.
        """
        return self.__fund_domain_list[self.__lookup_table[self.__symmetric_space.index(P)]]


    def orbit_representative_index(self, P):
        """
        Give the index of the element in the fundamental domain of
        P^1(Z/NZ) equivalent to the point P, with respect to the
        ordering given in fundamental_domain().
        """
        return self.__lookup_table[self.__symmetric_space.index(P)]


    def embed_element_via_level_splitting(self, q):
        """
        Returns a 2 x 2 matrix over Z/NZ given by embedding a
        quaternion via the level splitting.

        WARNING: THIS MAY NOT BE DEFINED FOR AN ARBITRARY
        ELEMENT OF THE ALGEBRA, BUT IT IS ALWAYS DEFINED FOR
        THE RING OF INTEGERS WE HAVE STORED.
        """
        N_split = self.level_at_split_primes()
        embed_list = self.__basis_embedding_vector
        q_vec = vector(q)   ## Note: This replaces q.vector()
        try:
            M = sum([(q_vec[s] * embed_list[s]) % N_split  for s in range(4)]) % N_split
        except:
            raise RuntimeError, "Oops!  The embedding failed... are you dividing be the level" + str(N_split) + "somewhere?"

        return M



    def elements_of_norm__half(self, m):
        """
        Returns the integral elements of reduced norm m,
        as vectors in the integral basis (up to +/-1).
        """
        ## Generate additional vectors if we don't have enough
        L = len(self.__pos_vector_list_of_small_length)
        if m >= L:
            print "We only stored integral elements of norm <= " + str(L) + ", now computing to " + str(m) + "."  
            self.__pos_vector_list_of_small_length = self.__positive_vectors_of_small_length(m)

        ## Return the list
        return self.__pos_vector_list_of_small_length[m]




    def elements_up_to_units_of_norm(self, m):
        """
        Compute elements of the maximal order of H of reduced norm m up to unit multiples.
        (These give the (sub)ideal of the maximal order of index p^2.)
        """
        ## List the units
        U = self.units()

        ## List the elements of norm m (up to +/-1)
        m_elts = Set([self.element_from_integral_basis_coordinates(v) for v in self.elements_of_norm__half(m)])

        ## Determine representatives up to equivalence -- (There will be p+1 of these up to equivalence when m = p)!
        eq_repns = []
        while len(m_elts) > 0:
            x = list(m_elts)[0]                    ## << -----------------  CHANGE THIS TO USE m_elts.pop()!!!
            x_eq_set = Set([u*x  for u in U])
            m_elts = m_elts.difference(x_eq_set)     ## Remove all elts in the orbit of x
            eq_repns.append(x)

        return eq_repns


    def __prepare_hecke_action(self):
        """
        ADD DOCUMENTATION...

        Setup the P^1(N'), orbits, and lookup table for quickly
        computing the Hecke action.
        """
        ## Make a copy of P^1(Z/N'Z)
        N_split = self.level_at_split_primes()
        P1 = P1List(N_split).list()           ## <--- Perhaps Lassina can take advantage of this?!? =)

        ## Make a list of symmetric spaces for p|N where p|D
        S_list = []
        N = self.level()
        for p in self.bad_level_primes():
            Q_ring = QuaternionLocalQuotientRingRamified(self.quaternion_algebra(), self.basis_for_maximal_order(), p, valuation(N,p))
            units = [x  for x in Q_ring.list_of_elements() if x.lift().reduced_norm() % Q_ring.prime() != 0]
            S_list.append(units)

        ## Make the "global" symmetric space
        Symmetric_space = product_as_tuples(S_list + [P1])


        ## Compute the orbits and a fundamental domain (for the global symmetric space)
        U = self.units()
        F = []
        F_orbits = []
        S_set = Set(Symmetric_space)
        while S_set.cardinality() > 0:
            P = list(S_set)[0]                    ## << --------------------- CHANGE THIS TO USE m_elts.pop()!!!
            P_orbit = Set([self.action_on_symmetric_space_with_level(u,P)  for u in U])   ## Note: This is even ok for level 1! =)
            S_set = S_set.difference(P_orbit)     ## Remove all elts in the orbit of x
            F_orbits.append(P_orbit)
            F.append(P)


        ## Make lookup table
        lookup_table = []
        for i in range(len(Symmetric_space)):
            Q = Symmetric_space[i]
            j = 0
            while not Q in F_orbits[j]:
                j += 1
            lookup_table.append(j)         ## Here lookup_table[i] stores the index of the orbit of the element Symmetric_space[i]


        ## Store the orbit information 
        self.__symmetric_space = Symmetric_space
        self.__P1_N = P1
        self.__list_of_ramified_symmetric_spaces = S_list

        self.__fund_domain_list = F
        self.__lookup_table = lookup_table



    def action_on_symmetric_space_with_level(self, q, P):
        """
        Gives an action of q on point P in the product:

            S = (all local symmetric spaces for primes p|D) x (P1(Z/N'Z))

        where N' is the part of the level prime to D.
        """
        ## Compute the action of q on the last component (representing the split part of the symmetric space)
        N_split = self.level_at_split_primes()
        M = self.embed_element_via_level_splitting(q)
        new_p = M * Matrix(ZZ, 2, 1, P[-1])
        new_p_tuple_normalized = p1_normalize(N_split, ZZ(new_p[0,0]), ZZ(new_p[1,0]))[:2]

        ## Check that this action is non-degenerate (i.e., gives a non-degenerate point in P^1(Z/N'Z))
        if (new_p_tuple_normalized == (0,0)) and (N_split > 1):
            raise RuntimeError, "The action on this point of P^1(Z/N'Z) is degenerate!" 

        ## Create the product (of the non-degenerate local actions)
        new_P = tuple([s_comp.act_on_units_by_quaternion(q)  for s_comp in P[:-1]] + [new_p_tuple_normalized])

        ## Return the new point (as a tuple)!
        return new_P


    def action_on_P1_with_level(self, q, P):
        """
        Gives an action of q on point P = (u,v)
        (in P1(Z/NZ)) given by the pre-defined level splitting.
        """
        N_split = self.level_at_split_primes()
        M = self.embed_element_via_level_splitting(q)

        ## Compute the action of M on p
        new_p = M * Matrix(ZZ, 2, 1, P)

        ## Return the normalized tuple (defining a non-degenerate point in P^1(Z/NZ))
        new_p_tuple_normalized = p1_normalize(N_split, ZZ(new_p[0,0]), ZZ(new_p[1,0]))[:2]
        if new_p_tuple_normalized != (0,0):
            return new_p_tuple_normalized
        else:
            ## Only raise an error if the level is bigger than one!
            if (N_split > 1):
                raise RuntimeError, "The action on this point of P^1(Z/NZ) is degenerate!" 
            else:
                return P



    def brandt_matrix_by_explicit_action(self, m):
        """
        Return the Brandt matrix for the natural number m relatively
        prime to the discriminant.
        """
        ## Check that m doesn't divide D
        if GCD(self.discriminant(), m) == 0:
            raise NotImplementedError, "Sorry, we can't compute at factors dividing the discriminant yet... =("

        ## Compute the matrix, one row at a time
        Reps = self.elements_up_to_units_of_norm(m)
        Fund = self.fundamental_domain()
        n = len(Fund)
        row_list = []
        for P in Fund:            
            P_mult_list = [0  for i in range(n)]
            for r in Reps:
                try:
                    P_mult_list[self.orbit_representative_index(self.action_on_symmetric_space_with_level(r, P))] += 1
                except:
                    pass         ## Don't count points where the action is degenerate -- only happens when p | N.
            row_list.append(P_mult_list)

        ## Create the matrix
        BM = Matrix(ZZ, n, n, row_list)

        ## Return the result
        return BM


    def brandt_matrix_at_prime(self, p):
        """
        Returns the Brandt matrix at the prime p with respect to the
        basis given by fundamental_domain().

        Warning:  This only works when (p, D) = 1, but ok if (p,N) > 1. 

        Note:  The results are always cached! =)
        """
        ## Sanity Check
        if not is_prime(p):
            raise TypeError, "p must be a prime > 0."

        ## Check if it is already computed!
        p_index = prime_range(p+1).index(p)
        try:
            if self.__brandt_matrix_list_at_prime_powers[p_index] != None:
                return self.__brandt_matrix_list_at_prime_powers[p_index][0]
        except:
            brandt_len = len(self.__brandt_matrix_list_at_primes)
            for i in range(p_index - brandt_len + 1):
                self.__brandt_matrix_list_at_prime_powers.append(None)
            
        ## Create the matrix
        BM = self.brandt_matrix_by_explicit_action(p)

        ## Cache the result
        self.__brandt_matrix_list_at_prime_powers[p_index] = [BM]

        ## Return the result
        return BM


    def brandt_matrix_at_prime_power(self, p, r, weight=2):
        """
        Return the Brandt matrix for the prime power p^r relatively
        prime to the discriminant D (but not necessarily prime to the level N).

        Note:  The results are always cached! =)
        """
        ## Some useful aliases
        Bp = brandt_matrix_at_prime(p)         ## Note: This also instantiates the cached list entries through p_index.
        p_index = prime_range(p+1).index(p)
        B_list = self.__brandt_matrix_list_at_prime_powers[p_index]    ## NOTE: This is a pointer to the cahced list!

        ## Compute prime power Brandt matrices up to the relevant power -- caching the result!
        while len(B_list) < r:
            B_new = B_list[-1] * Bp - (p ** (weight-1)) * B_list[-2]   ## Create the Brandt matrix from the Hecke
            B_list.append(B_new)                                       ## algebra relations (and the weight).

        ## Return the result
        return B_list[r-1]


    def brandt_matrix(m):
        """
        Return the Brandt matrix for the natural number m relatively
        prime to the discriminant D.

        Warning:  This only works when (m, D) = 1, but is ok if (m,N) > 1. 

        Note:  The results are always cached (by the prime powers appearing in m)! =)
        """
        return prod([self.brandt_matrix_at_prime_power(p, r)  for (p,r) in factor(m)])  ## Note: The order doesn't matter
                                                                                        ## here since it's commutative!



            

## -------------------- Find the short vectors in the maximal order ----------------------


    def __positive_vectors_of_small_length(self, m):
        """
        Enumerates all vectors of reduced norm <= M with respect to
        our specified basis for the maximal order.

        TO DO: Fix the conversion routine for creating a quadratic form from a matrix!        
        """
        R_basis = self.basis_for_maximal_order()
	M = Matrix(ZZ, 4, 4, [(x*y.conjugate()).reduced_trace()  for x in R_basis  for y in R_basis])
	Q = QuadraticForm(M)
        
        return Q.vectors_by_length(m)


## -------------------- Splitting of the level N Structure -----------------------

    def __quaternionic_splitting_at_prime_power(self, p, e):
        """
        Returns two matrices which give a surjection 
        of the maximal order R of the quaternion algebra 
        H = (-1, -1) into M_{2x2}(Z/(p^e)Z) 

        More precisely, it gives an explicit isomorphism

            R tensor Z/(p^e)Z -=-> M_2(Z/(p^e)Z)

        by returning values a,b defining the images of 
        i and j (in this case only), as

             i |--> [0  1]      j |--> [a   b]
                    [-1 0]             [b  -a]

        """
        ## Take random b and try to solve a^2 + b^2 + 1 = 0 mod p^e
        while True:
            b = ZZ.random_element(1, p)     ## Note: This replaces "random_int_upto(p)"
            PR = PolynomialRing(QQ, 'zzz')
            zzz = PR.gen()
            f = PR(zzz*zzz + (b*b + 1))
            #print f
            f_factorization = f.factor_padic(p, e+1)
            if len(f_factorization) != 1:                     ## Check if the polynomial factors!
                a = ZZ(-f_factorization[0][0][0]) % (p**e)
                return a, b    



    def __store_quaternionic_level_splitting(self):
        """
        Compute a 'global' splitting (mod N) of the maximal order 
        in terms of the integers a and b, as defined in 
        quaternionic_splitting_at_prime_power(p,e)

        This computes and stores the image of one, iii, jjj, and kkk
        in GL2(Z/NZ).

        WARNING: WE SHOULD PROBABLY ALWAYS USE THE Z-BASIS FOR THE
        RING OF INTEGERS HERE, SINCE THERE MAY BY ISSUES FOR PRIMES
        DIVIDING N AND THE INDEX OF THE USUAL ORDER IN THE MAXIMAL ONE!!!
        """
        ## Find the prime power splittings
        N_split = self.level_at_split_primes()
        F = factor(N_split)
        a_list = []
        b_list = []
        for f in F:
            a, b = self.__quaternionic_splitting_at_prime_power(f[0], f[1])
            a_list.append(a)
            b_list.append(b)


        self.__N_split_factor_list = F
        self.__a_list = a_list
        self.__b_list = b_list


        ## Compute the lifting to mod N_split    
        E = crt_basis([f[0] ** f[1]  for f in F])
        A = sum([a_list[s] * E[s]  for s in range(len(F))]) % N_split
        B = sum([b_list[s] * E[s]  for s in range(len(F))]) % N_split

        self.__j_embedding_A = A
        self.__j_embedding_B = B

        ## Construct the matrices defining the embedding
        #IntegerModRing(N)
        A1 = Matrix(ZZ, 2,2, [0, 1, -1, 0])
        B1 = Matrix(ZZ, 2,2, [A, B, B, -A])

        self.__basis_embedding_vector = [Matrix(ZZ, 2, 2, [1,0,0,1]), A1, B1, A1 * B1]

        ##return A1, B1




