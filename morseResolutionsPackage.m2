
newPackage(
    "MorseResolutions",
    Version => "1.0.1",
    Date => "March 1, 2023",
    Headline => "morse resolutions",
    Authors => {
	{ 
	    Name => "Trung Chau",
	    Email => "trung.chau@utah.edu", 
	    HomePage => "https://www.math.utah.edu/~chau/"
	    },
	{ 
	    Name => "Selvi Kara",
	    Email => "selvikara@gmail.com", 
	    HomePage => "www.selvikara.com"
	    },
	{ 
	    Name => "Augustine O'Keefe",
	    Email => "aokeefe@conncoll.edu ", 
	    HomePage => "https://www.conncoll.edu/directories/faculty-profiles/augustine-okeefe/"
	    },
	}
    AuxiliaryFiles => false,
    DebuggingMode => false
    )

export {
    -- Methods
    "taylorCell",
    "allTaylorCells",
    "bridge",
    "smallestBridge", 
    "possibleEdgesWithPositions",    
    "possibleEdges",    
    "bMMatching", 
    "bridgeFriendly",
    "criticalBMCells",
    "bMRanks", 
    "lyubeznikBridge",
    "lyubeznikMatching",
    "criticalLyubeznikCells",
    "lyubeznikRanks",
    "possibleTrimmedEdges",    
    "trimmedMatching", 
    "criticalTrimmedCells",
    "trimmedRanks",
    }

-------------------
-- Exported Code
-------------------


---------------------------------------------------------------
---------------------------------------------------------------
-- Auxiliary functions: subsets of minimal generating set of a 
-- monomial ideal
---------------------------------------------------------------
---------------------------------------------------------------

-----------------------------------------
--Taylor Cells of Cardinality k-
-----------------------------------------
taylorCell = method(TypicalValue => List)
taylorCell(Ideal,ZZ) := List => (I,k)->(
    select(subsets flatten entries gens I, i-> #i==k)
    );

-----------------------------------------
--Taylor Cells-
-----------------------------------------
allTaylorCells = method(TypicalValue => List) 
allTaylorCells(Ideal):= List => I->(
    M= flatten entries gens I;
    L=for k from 0 to #M-1 list taylorCell(I,#M-k);
    L
    );


-----------------------------------------------------------
-----------------------------------------------------------
-- Main Barile-Macchia resolution functions
-----------------------------------------------------------
-----------------------------------------------------------

-----------------------------------------
--Bridge-
-----------------------------------------
bridge = method(TypicalValue => List)
bridge(List) := List => L ->(
    if #L<3 then {} else select(L, i -> lcm L == lcm delete(i,L))
     );

-----------------------------------------
--Smallest Bridge-
-----------------------------------------
smallestBridge = method(TypicalValue => RingElement)
smallestBridge(List, Sequence) := RingElement => (L, S) ->(
    if bridge L=!={} then (
	sortB = select(S, i-> member(i,bridge L)); --select returns a list in the same order as the input list
    	sortB_0
	)
    else print "no bridges exist"
    );

-----------------------------------------------
--Possible Edges of a Barile-Macchia Matching-
-----------------------------------------------

---Part 1: Possible Edges of a Barile-Macchia Matching with Positions of the Smallest Bridges--


possibleEdgesWithPosition = method(Dispatch => Thing)
possibleEdgesWithPosition(Sequence) := List => S -> (
    I = ideal S;
    Sigma = drop(allTaylorCells I, -2); --drops the Taylor Cells of length 1 and 2
    Omega = flatten drop(allTaylorCells I, -2);
    A={};
    i = 0;
    j = 0;
    while #Omega >0 do(
    	sigma = Sigma_i_j;
    	if isSubset({sigma}, Omega) then(
    	    if bridge sigma =!= {} then(
	    	sb = smallestBridge(sigma, S);
	    	sigmaMinusSb = delete(sb, sigma);
	    	A = append(A, (position(S, k-> sb==k), sigma, sigmaMinusSb));
	    	Omega = delete(sigma, Omega);
	    	Omega = delete(sigmaMinusSb, Omega);
	    	)
    	    else Omega = delete(sigma, Omega);
    	);
    if #(Sigma_i)> j+1 then j = j+1 else(i = i+1; j = 0);
    );
    A
    );



-- Part 2: Possible Edges of a Barile-Macchia Matching --

possibleEdges = method(Dispatch => Thing)
possibleEdges(Sequence) := List => S -> ( 
    A=possibleEdgesWithPosition S;
    B={};
    for i from 0 to #A-1 do(
	B=append(B,delete (A_i_0, A_i));
	);
    return B;
    )


-----------------------------------------
--Barile-Macchia Matching-
-----------------------------------------
bMMatching = method(Dispatch => Thing)
bMMatching(Sequence) := List => S -> (
    A = possibleEdgesWithPosition S;
    groupedA = hashTable apply(A, i->(i_2, select(A,j->j_2==i_2)));
    minA = applyValues(groupedA, i-> min i);
    Bridge = apply(values minA, i->drop(i,1));
    Bridge
    );


-----------------------------------------
--isBridge Friendly-
-----------------------------------------

isBridgeFriendly = method(Dispatch => Thing)
isBridgeFriendly(Sequence) := List => S -> (
    A = possibleEdges S;
    B =  bMMatching S;
    A==B
    );

-----------------------------------------
--Friendly Step-
-----------------------------------------
friendlyStep = method(Dispatch => Thing)
friendlyStep(Sequence) := List => S -> (
    A = possibleEdges S;
    B = bMMatching S;
    {B, A==B}
    );


-----------------------------------------
--Bridge Friendly List-
-----------------------------------------
bridgeFriendlyList = method(TypicalValue => List)
bridgeFriendlyList(Ideal) := List => I -> (
    -- take all permutations of S, find bMMatching, check if second component is true for any of them
    orderings = permutations flatten entries gens I;
    Bridges = apply(orderings, i-> {i}|friendlyStep(toSequence i)); --output is {S, M}
    friendlies = select(Bridges, i -> i_2); --i_2 is Boolean so this will only select true guys
    apply(friendlies, i->drop(i,-1))
    );


-----------------------------------------
--Critical Barile-Macchia Cells -
-----------------------------------------
criticalBMCells = method(Dispatch => Thing)
criticalBMCells(Sequence) := List => S -> (
    I = ideal S;
    crit = allTaylorCells I;
    n = #crit;
    nonCrit = bMMatching(S);
    for i from 0 to #nonCrit-1  do(
        k = #nonCrit_i_0;
        sigma1 = nonCrit_i_0;
        sigma2 = nonCrit_i_1;   
        crit1 = crit_(n-k);
        crit2 = crit_(n-k+1);
        crit1 = delete(sigma1, crit1);
        crit2 = delete(sigma2, crit2);
        crit = replace(n-k, crit1, crit);
        crit = replace(n-k+1, crit2, crit);
    );
    crit
    );

-----------------------------------------
--Barile-Macchia Rank -
-----------------------------------------
bMRanks = method(Dispatch => Thing)
bMRanks(Sequence) := List => S -> (
    crit = criticalBMCells(S);
    n = #crit;
    rankList = {1};
    for i from 0 to (n-1) do (
        rankList = append(rankList, #crit_(n-i-1) );
        );
    rankList
    );


-----------------------------------------------------------
-----------------------------------------------------------
-- Main Lyubeznik resolution functions
-----------------------------------------------------------
-----------------------------------------------------------

-----------------------------------------
--Lyubeznik Bridge -
-----------------------------------------
lyubeznikBridge = method(TypicalValue => List)
lyubeznikBridge(List,Sequence) := RingElement => (L,S) ->(
    if #L<2 then print "The Taylor cell does not contain a Lyubeznik
bridge"
    else A={};
for i from 0 to #S-1 do(
    B=S_i;
    L=delete(B,L);
    if ( #L>0 and lcm L // B !=0) then (
	  A=B;
	  break
	  );
    );
A
);


-----------------------------------------
--Lyubeznik Matching -
-----------------------------------------
lyubeznikMatching = method(Dispatch => Thing)
lyubeznikMatching(Sequence) := List => S -> (
    I = ideal S;
    Omega = flatten drop(allTaylorCells I, -2);
    LMatching={};
    while #Omega >0 do(
    	sigma = Omega_0;
    	if lyubeznikBridge(sigma,S) =!= {} then(
	    	sb = lyubeznikBridge(sigma, S);
	    	sigmaMinusSb = delete(sb, sigma);
	    	LMatching = append(LMatching, (sigma, sigmaMinusSb));
	    	Omega = delete(sigma, Omega);
	    	Omega = delete(sigmaMinusSb, Omega);
	    	)
    	    else Omega = delete(sigma, Omega);
    );
    LMatching
    );

-----------------------------------------
--Critical Lyubeznik Cells -
-----------------------------------------
criticalLyubeznikCells = method(Dispatch => Thing)
criticalLyubeznikCells(Sequence) := List => S -> (
    I = ideal S;
    crit = allTaylorCells I;
    n = #crit;
    L = lyubeznikMatching(S);
    for i from 0 to #L-1  do(
        k = #L_i_0;
        sigma1 = L_i_0;
        sigma2 = L_i_1;   
        crit1 = crit_(n-k);
        crit2 = crit_(n-k+1);
        crit1 = delete(sigma1, crit1);
        crit2 = delete(sigma2, crit2);
        crit = replace(n-k, crit1, crit);
        crit = replace(n-k+1, crit2, crit);
    );
    crit
    );

-----------------------------------------
--Lyubeznik Rank -
-----------------------------------------

lyubeznikRanks = method(Dispatch => Thing)
lyubeznikRanks(Sequence) := List => S -> (
    crit = criticalLyubeznikCells(S);
    n = #crit;
    rankList = {1};
    for i from 0 to (n-1) do (
        rankList = append(rankList, #crit_(n-i-1) );
        );
    rankList
    );

----------------------------------------
--Trimmed Lyubeznik resolution via Barile-Macchia algorithm
----------------------------------------

-----------------------------------------------
--Possible Edges of a Barile-Macchia Matching of the Lyubeznik Complex-
-----------------------------------------------

possibleTrimmedEdges = method(TypicalValue => List)
possibleTrimmedEdges(Sequence, Sequence) := List => (S1,S2) -> (
    B= criticalLyubeznikCells S1;
    T= select(B,j->j=!={});
    Sigma = drop(T, -2); 
    Omega = flatten drop(T, -2);
    A={};
    i = 0;
    j = 0;
    while #Omega >0 do(
    	sigma = Sigma_i_j;
    	if isSubset({sigma}, Omega) then(
    	    if bridge sigma =!= {} then(
	    	sb = smallestBridge(sigma, S2);
	    	sigmaMinusSb = delete(sb, sigma);
	    	A = append(A, (position(S2, k-> sb==k), sigma, sigmaMinusSb));
	    	Omega = delete(sigma, Omega);
	    	Omega = delete(sigmaMinusSb, Omega);
	    	)
    	    else Omega = delete(sigma, Omega);
    	);
    if #(Sigma_i)> j+1 then j = j+1 else(i = i+1; j = 0);
    );
    A
    );

-----------------------------------------------
--Trimmed Barile-Macchia Matching of the Lyubeznik Complex
-----------------------------------------------


trimmedMatching = method(TypicalValue => List)
trimmedMatching(Sequence, Sequence) := List => (S1,S2) -> (
    A = possibleTrimmedEdges(S1,S2);
    groupedA = hashTable apply(A, i->(i_2, select(A,j->j_2==i_2)));
    minA = applyValues(groupedA, i-> min i);
    Bridge = apply(values minA, i->drop(i,1));
    Bridge
    );


-----------------------------------------------
--Critical Cells of the Trimmed Lyubeznik Complex
-----------------------------------------------

criticalTrimmedCells = method(TypicalValue => List)
criticalTrimmedCells(Sequence, Sequence) := List => (S1,S2) -> (
    crit = criticalLyubeznikCells S1;
    n = #crit;
    nonCrit = trimmedMatching(S1,S2);
    for i from 0 to #nonCrit-1  do(
        k = #nonCrit_i_0;
        sigma1 = nonCrit_i_0;
        sigma2 = nonCrit_i_1;   
        crit1 = crit_(n-k);
        crit2 = crit_(n-k+1);
        crit1 = delete(sigma1, crit1);
        crit2 = delete(sigma2, crit2);
        crit = replace(n-k, crit1, crit);
        crit = replace(n-k+1, crit2, crit);
    );
    crit
    );

-----------------------------------------------
--Trimmed Rank of the Lyubeznik Complex
-----------------------------------------------

trimmedRanks = method(TypicalValue => List)
trimmedRanks(Sequence, Sequence) := List => (S1,S2) -> (
    crit = criticalTrimmedCells(S1,S2);
    n = #crit;
    rankList = {1};
    for i from 0 to (n-1) do (
        rankList = append(rankList, #crit_(n-i-1) );
        );
    rankList
    );

----------------------------------------
--Documentation
----------------------------------------
beginDocumentation()

doc///
Node
Key
   MorseResolutions
Headline
    A package for working with Morse resolutions of monomial ideals
Description
  Text
    {\em MorseResolutions} package enables computations for Morse resolutions of monomial ideals. 
    In particular, this package allows computations for the two major classes of Morse resolutions: 
    Barile-Macchia resolutions from [CK] and Lyubeznik resolutions from [BW]. Morse resolutions are 
    introduced in [BW] and induced by homogeneous acyclic matchings using discrete Morse theory. 
    
    This package constructs two classes of homogeneous acyclic matchings (Barile-Macchia matchings and Lyubeznik matchings) 
    of a monomial ideal $I$ with respect to a total order on its minimal generators. These matchings induce Barile-Macchia 
    resolutions and Lyubeznik resolutions.  We use Algorithm 3.6 [CK] to construct the Barile-Macchia matching function. 
    Similarly, we use the matching from Theorem 3.2 [BW] to construct the Lyubeznik matching function. The package 
    also contains functions for computing the ranks of Barile-Macchia resolutions and Lyubeznik resolutions induced 
    by the Barile-Macchia matchings and Lyubeznik matchings, respectively.
    
    This package also contains procedures to check bridge-friendliness of monomial ideals as described 
    in Definition 2.24 [CK]. 
    
    In [CK], Barile-Macchia algorithm are applied to the Taylor complex of a monomial ideal. Instead of the Taylor complex, 
    one can apply the Barile-Macchia algorithm to a simplicial complex that supports a free resolution of $I$ by [BW]. 
    This package contains a function that computes the Barile-Macchia matching of a Lyubeznik complex, a simplicial complex 
    that supports a free resolution of $I$ with respect to a fixed total order $<$ on the minimal generating set of $I$.
    
    The goal of this work was primarily to help compute examples in the paper [CK]. This is a work in progress and the 
    authors are working to improve the functionality of this package. All suggestions and contributions are welcome.
    
    Here is a typical use of this package. We create an ideal in 4 variables with the total order described 
    in the sequence $S$. 
     
Acknowledgement
    We thank Jeremy Dewar for helpful discussions.
References
    [CK] T. Chau and S. Kara, Barile-Macchia Resolutions. Preprint, @arXiv "2211.04640"@ (2022).
    [BW] E. Batzies and V. Welker, Discrete Morse theory for cellular resolutions, J. Reine Angew. Math. 543 (2002).  
Subnodes
          taylorCell
          allTaylorCells
          bridge
          smallestBridge
          possibleEdgesWithPositions
          possibleEdges
          bMMatching
          bridgeFriendly
          criticalBMCells
          bMRanks
          lyubeznikBridge
          lyubeznikMatching
          criticalLyubeznikCells
          lyubeznikRanks
          possibleTrimmedEdges
          trimmedMatching
          criticalTrimmedCells
          trimmedRanks
///







doc///
Node 
Key
    taylorCell 
    (taylorCell, Ideal, ZZ)  
Headline
    prints all subsets of a fixed cardinality $n$ of a minimal generating set of the given monomial ideal $I$
Usage
    taylorCell(I,n)
Inputs
    I: Ideal
    n: ZZ
Outputs
    :List
    	a list that consists of all subsets of a minimal monomial generating set of $I$ with cardinality $n$
Description
  Text
      Given a monomial ideal $I$ and an integer $n$, returns cardinality $n$ subsets of minimal generators of $I$. In other words,
      it returns all $(n-1)$-faces of the Taylor complex of $I$.     
  Example
      R=QQ[a,b,c,d];
      S = (c*d, b*c, a*b, a^2*d);
      I=ideal(S);
      taylorCell(I,2)
SeeAlso
    allTaylorCells
///


doc ///
Node 
Key
    allTaylorCells
    (allTaylorCells, Ideal)  
Headline
    prints all subsets of a minimal generating set of the given monomial ideal $I$
Usage
    allTaylorCells(I)
Inputs
    I: Ideal
Outputs
    :List
    	a list of all subsets of a minimal generating set of I
Description
  Text
      Given an ideal $I$, returns all subsets of a minimal generating set of $I$. In other words, it returns all faces of 
      the Taylor complex of $I$.    
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a^2*d);
      I=ideal(S);
      allTaylorCells(I)
SeeAlso
    taylorCell
///


-----------------------------
-- Barile-Macchia Documentation
-----------------------------

doc ///
Node 
Key
    bridge 
    (bridge, List)  
Headline
    prints all bridges of a list of monomials
Usage
    bridge(L)
Inputs
    L: List
        a list of monomials
Outputs
    :List
    	if no bridge exists, returns the empty list {}, otherwise returns	a list containing all bridges of $L$
Description
  Text
      Given a list of monomials $L$, returns all bridges of $L$. 
      
      A monomial $m$ in $L$ is called a bridge of $L$ if the lcm of L does not change after removing $m$. 
          
  Example
      R=QQ[a,b,c,d,e];
      L={a*b,a*d,a*e};
      bridge(L) 
       
SeeAlso
    smallestBridge
///

doc ///
Node 
Key
    smallestBridge 
    (smallestBridge, List, Sequence)  
Headline
    prints the smallest bridge of a list of monomials with respect to a total order
Usage
    smallestBridge(L,S)
Inputs
    L: List
    	a list of monomials
    S: Sequence
    	a sequence of monomials that contain monomials in L
	a total order on a set of monomials that contain monomials in L
Outputs
    :RingElement
Description
  Text
      Given a list of monomials $L$, returns the smallest bridge of $L$ with respect to the total order $S$.
      
  Example
      R=QQ[a,b,c,d,e];
      L={a*b,b*c,c*d,d*e};
      S=(d*e,c*d,b*c,a*b);
      smallestBridge(L,S) 
      
SeeAlso
    bridge 
///

doc ///
Node 
Key
    possibleEdgesWithPositions 
    (possibleEdgesWithPositions, Sequence)  
Headline
    prints triples that contain  positions of the corresponding smallest bridges associated to possible edges and possible edges
    of the Taylor complex of a monomial ideal with respect to a given total order monomial ideal with respect to a given total 
    order before Step 3 of Algorithm 2.6 in [CK].
Usage
    possibleEdgesWithPositions(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Given a monomial ideal $I$, let $<$ be a total order on its minimal generating set $G(I) = \{m_1,\ldots,m_n\}$.
      The total order $<$ is recorded as a sequence $S$ of $\{m_1,\ldots,m_n\}$.
      
      Let $G$ be the directed graph obtained from the Taylor complex of $I$. Directed edges of $G$ are of the  
      form $(\sigma,\tau)$ where $\tau\subset \sigma \subset G(I)$ and $|\tau|=|\sigma|-1$.  
      Consider a collection of directed edges $A$ in $G$. We call $A$ an acyclic matching in $G$ if
      	a) $A$ is a matching in $G$, i.e. none of the two edges in $A$ share vertices, and
	      b) there is no directed cycle in the graph obtained from $G$ by reversing the edges in $A$.
      An acyclic matching $A$ is called homogeneous if $\lcm(\sigma)=\lcm(\tau)$ for each directed edge $(\sigma,\tau) \in A$. 
      
      A collection of directed edges of $G$ produced by Algorithm 2.6 in [CK] is a homogeneous acyclic matching in $G$ by 
      Theorem 2.8 from [CK]. A matching that is produced by Algorithm 2.6 in [CK] is called a Barile-Macchia matching of $I$ or, more 
      precisely, a Barile-Macchia matching of the Taylor complex of $I$. The output of this algorithm depends on a choice of total 
      order on $G(I)$. In other words, each total order produces a Barile-Macchia matching of $I$, and it is worth noting that 
	these Barile-Macchia matchings are not necessarily the same.
      
      The edges in a Barile-Macchia matching are obtained by considering directed edges $(\sigma,\tau)$ where $\tau$ is obtained from 
      $\sigma$ by removing the smallest bridge of $\sigma$ with respect to $S$. Steps 1) and 2) of the algorithm puts together 
      such direct edges while making sure the source vertices of the considered edges are all distinct. These two steps can 
      create two directed edges $(\sigma,\tau)$ and $(\sigma',\tau')$ such that $\tau=\tau'$. In other words, after removing 
      the smallest bridges of $\sigma$ and $\sigma'$, it is possible to obtain the same target vertex. Step 3) of the algorithm 
      picks only one directed edge  $(\sigma,\tau)$ among those in a way that the smallest bridge of $\sigma$ is smaller than 
      the smallest bridges of all other source vertices whose targets overlap.
      
      The edges that are obtained from Steps 1) and 2) of the algorithm are called possible edges of the Barile-Macchia matching of the 
      Taylor complex of $I$ with respect to $S$. Given a total order $S$, this function returns to the list of triples 
      $(i, \sigma, \sigma \setminus \sbridge(\sigma))$, where $i$ is the position of the smallest bridge of $\sigma \subseteq \G(I)$ 
      with respect to a total order $S$ on $\G(I)$ and collection of all $(\sigma \setminus \sbridge(\sigma))$ is the possible edges of $I$.
       
       
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      possibleEdgesWithPositions(S)  
      
SeeAlso
    bMMatching
    possibleTrimmedEdges
    possibleEdges
///


doc ///
Node 
Key
    possibleEdges 
    (possibleEdges, Sequence)  
Headline
    prints all edges of a Barile-Macchia matching of the Taylor complex of a monomial ideal with respect to a given total order
    before Step 3 of Algorithm 2.6 in [CK]
Usage
    possibleEdges(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Given a monomial ideal $I$ and a given a total order $S$, this function returns to the list of potential edges 
      of the Barile-Macchia matching of the Taylor complex of $I$ with respect to $S$. 
       
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      possibleEdges(S)  
      
SeeAlso
    bMMatching
    possibleEdgesWithPositions
    possibleTrimmedEdges
///


doc ///
Node 
Key
    bMMatching 
    (bMMatching, Sequence)  
Headline
    prints all edges of a Barile-Macchia matching of the Taylor complex of a monomial ideal with respect to a given total order
Usage
    bMMatching(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Given a total order $S$ on $G(I)$ for a monomial ideal $I$, this function returns the Barile-Macchia matching with respect
	to $S$ of the Taylor complex of $I$.
      
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      bMMatching(S) 
       
SeeAlso
    possibleEdges
    lyubeznikMatching
    trimmedMatching
///

doc ///
Key
    isBridgeFriendly 
    (isBridgeFriendly, Sequence)  
Headline
    checks whether a monomial ideal $I$ with respect to a total order $S$ on $G(I)$ is bridge-friendly with respect to $S$
Usage
    isBridgeFriendly(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :Boolean
Description
  Text
      A monomial ideal $I$ is called bridge-friendly with respect to a total order $S$ on $G(I)$ if Step 3  
      of Algorithm 2.6 [CK] is redundant with respect to $S$, i.e., possibleEdges(S)=bMMatching(S).
      
      This function tests whether $I$ is bridge-friendly with respect to the given total order $S$ on $G(I)$. 
      
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      isBridgeFriendly(S)  
      
SeeAlso
    possibleEdges
    bMMatching
///


doc ///
Node 
Key
    friendlyStep 
    (friendlyStep, Sequence)  
Headline
    prints a list such that the first entry in the list is the Barile-Macchia matching of a monomial ideal $I$ with 
    respect to a given total order $S$ on $G(I)$ and the second entry is a Boolean to check if $I$ is 
    bridge-friendly with respect to $S$
Usage
    friendlyStep(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $I$ be a monomial ideal with the given total order $S$ on $G(I)$. This function returns to a pair where 
      the first element is the Barile-Macchia matching of $I$ with respect to $S$ and the second element in the list is 
      true or false depending on whether Barile-Macchia matching coincides with possible edges of $I$ with respect to $S$.
      
  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      friendlyStep(S)  
      
SeeAlso 
    possibleEdges
    bMMatching
    isBridgeFriendly
///


doc ///
Node 
Key
    bridgeFriendlyList
    (bridgeFriendlyList, Ideal)  
Headline
    prints a list of all Barile-Macchia matchings of the Taylor complex of a given monomial ideal with respect to total orders 
    for which $I$ is bridge-friendly with respect to each of those total orders.
Usage
    bridgeFriendlyList(I)
Inputs
    I: Ideal
    	a monomial ideal
Outputs
    :List
    	if no order exists, returns {}, otherwise returns a list containing all total orders on $G(I)$ which work
Description
  Text
      Given a monomial ideal $I$, this method computes all possible total orders $S$ on $G(I)$ with respect to which the ideal 
      $I$ is bridge-friendly. In particular, the output of this function is a list of pairs ${S, bMMatching(S)}$ where 
	$I$ is bridge-friendly with respect to $S$.
      
  Example
      R=QQ[a,b,c,d];
      I=ideal(a*b,b*c,c*a);
      bridgeFriendlyList(I)     
      
  Text
     The ideal in the following example is not bridge-friendly with respect to any total order. So, the output is {}. 
       
  Example
      R=QQ[a,b,c,d];
      I=ideal(c*d, b*c, a*b, a*d);
      bridgeFriendlyList(I)  
           
Caveat
    For a monomial ideal $I$ with $G(I)= \{m_1,\ldots,m_n\}$, there are $n!$ possible total orders on $G(I)$, so this 
    function can be computationally expensive.
    
SeeAlso
    possibleEdge
    bMMatching
    isBridgeFriendly
    friendlyStep 
///

doc ///
Node 
Key
    criticalBMCells 
    (criticalBMCells, Sequence)  
Headline
    prints all $A$-critical cells of the Taylor complex of a monomial ideal where $A$ is the Barile-Macchia matching of a monomial
    ideal $I$ with respect to a given total order on $G(I)$.
Usage
    criticalBMCells(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $I$ be the monomial ideal and $S$ be a total order on $G(I)$. Let $A$ be a homogeneous acyclic matching of $G$, 
      the directed graph obtained from the Taylor complex of $I$. A subset of $G(I)$ is called an $A$-critical cell of the 
      Taylor complex of $I$ if it does not appear in $A$.
      
      Given a total order $S$ on $G(I)$, this function returns to a list of all $A$-critical cells where $A$ is the Barile-Macchia 
      matching of the Taylor complex of $I$ with respect to $S$.
      
  Example
      R=QQ[a,b,c,d];
      S = (c*d, b*c, a*b, a*d);
      criticalBMCells(S) 
      
SeeAlso
    bMMatching
    criticalLyubeznikCells
    criticalTrimmedCells
///

doc ///
Node 
Key
    bMRanks 
    (bMRanks, Sequence)  
Headline
    prints the ranks of the free modules in the Barile-Macchia resolution of $R/I$ with respect to a total
    order on $G(I)$ where $I$ is a monomial ideal 
Usage
    bMRanks(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $G$ be the directed graph obtained from the Taylor complex of $I$. Each homogeneous acyclic matching on $G_X$ induces 
      a free resolution of $R/I$ by [BW]. More precisely, if $A$ is a homogeneous acyclic matching on $G_X$, then there exists a 
      CW-complex $X_A$ which supports a free resolution of $I$. The $i$-cells of $X_A$ are in one-to-one correspondence with 
      the $A$-critical cells of $X$ of cardinality $i+1$. The cellular resolution supported on $X_A$ is $\mathcal{F}_A$ where 
      $(\mathcal{F}_A)_i$ is the free $R$-module with a basis indexed by all critical subsets of cardinality $i$.
      
      
      Given a total order $S$ on $G(I)$ for a monomial ideal $I$, this function returns to ranks of the free modules of the 
      Barile-Macchia resolution of $I$ with respect to $S$. The output is a list of numbers where the $i^{th}$ number in the 
      list is the rank of $(\mathcal{F}_A)_i$.
      
  Example
     R=QQ[a,b,c,d];
     S = (c*d, b*c, a*b, a*d);
     bMRanks(S)
     
References
    [BW] E. Batzies and V. Welker, Discrete Morse theory for cellular resolutions, J. Reine Angew. Math. 543 (2002).    
    
SeeAlso
    bMMatching
    criticalBMCells
    criticalLyubeznikCells
    criticalTrimmedCells
///



-----------------------------
-- Lyubeznik Documentation
-----------------------------

doc ///
Node 
Key
    lyubeznikBridge 
    (lyubeznikBridge, List, Sequence)  
Headline
    prints the Lyubeznik bridge of a list of monomials with respect to a total order
Usage
    lyubeznikBridge(L,S)
Inputs
    L: List
    	a list of monomials
    S: Sequence
    	a sequence of all monomials in L
	a total order on a set of monomials in L
Outputs
    :RingElement
Description
  Text
      Given a list of monomials $L$, returns the Lyubeznik bridge of $L$ with respect to the total 
      order $S$. 
      
  Example
      R=QQ[x_1..x_8];
      S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
      L= {x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4};
      lyubeznikBridge(L,S)
      
SeeAlso
    smallestBridge
///


doc ///
Node 
Key
    lyubeznikMatching 
    (lyubeznikMatching, Sequence)  
Headline
    prints all edges of a Lyubeznik matching of a monomial ideal generated by $S$
Usage
    lyubeznikMatching(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $I$ be a monomial ideal with a total order $S$ on $G(I)$ and $G$ be the directed graph obtained from
      the Taylor complex of $I$. We call the homogeneous acyclic matching $A$ from Theorem 3.2 [BW] a Lyubeznik
      matching of $I$ with respect to a total order $S$. 
      
      Given a total order $S$ on $G(I)$, this function returns to the Lyubeznik matching of the Taylor complex of
      $I$ with respect to $S$.

  Example
      R=QQ[a,b,c,d]
      S = (c*d, b*c, a*b, a*d);
      lyubeznikMatching(S) 
      
References
    [BW] E. Batzies and V. Welker, Discrete Morse theory for cellular resolutions, J. Reine Angew. Math. 543 (2002).  
 
SeeAlso
    bMMatching
    trimmedMatching
///



doc ///
Node 
Key
    criticalLyubeznikCells 
    (criticalLyubeznikCells, Sequence)  
Headline
    prints all $A$-critical cells of the Taylor complex of a monomial ideal where $A$ is the Lyubeznik matching of a monomial
    ideal $I$ with respect to a given total order on $G(I)$
Usage
    criticalLyubeznikCells(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Given a total order $S$ on $G(I)$ for a monomial ideal $I$, this function returns to a list of all $A$-critical cells 
      where $A$ is the Lyubeznik matching of the Taylor complex of $I$ with respect to $S$.
      
  Example
      R=QQ[x_1..x_8];
      S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);	
      criticalLyubeznikCells(S)
      
SeeAlso
    lyubeznikMatching
    criticalBMCells
    criticalTrimmedCells 
///

doc ///
Node 
Key
    lyubeznikRanks 
    (lyubeznikRanks, Sequence)  
Headline
    prints the ranks of the free modules in the Lyubeznik resolution of a monomial ideal $I$ with respect to a total
    order on $G(I)$ 
Usage
    lyubeznikRanks(S)
Inputs
    S: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $A$ be the Lyubeznik matching of the Taylor complex of $I$ with respect to a total order $S$ on $G(I)$. Then 
      there exists a simplicial complex $X_A$ which supports a free resolution of $I$ by [BW] and [M]. We call the 
      simplicial complex $X_A$ the Taylor complex of $I$ with respect to $S$. The $i$-cells of $X_A$ are in one-to-one 
      correspondence with the $A$-critical cells of $X$ of cardinality $i+1$. The cellular resolution supported on $X_A$ 
      is $\mathcal{F}_A$ where $(\mathcal{F}_A)_i$ is the free $R$-module with a basis indexed by all critical subsets of 
      cardinality $i$.
      
      Given a total order $S$ on $G(I)$ for a monomial ideal $I$, this function returns the ranks the free modules of the 
      Lyubeznik resolution of $R/I$  with respect to $S$. The output is a list of numbers where the $i^{th}$ number in the 
      list is the rank of $(\mathcal{F}_A)_i$.
            
  Example
     R=QQ[a,b,c,d];
     S = (c*d, b*c, a*b, a*d);
     lyubeznikRanks(S)
     
References
    [BW] E. Batzies and V. Welker, Discrete Morse theory for cellular resolutions, J. Reine Angew. Math. 543 (2002).    
    [M]  J. Mermin. Three simplicial resolutions. Progress in commutative algebra, 1:127–141, (2012).
    
SeeAlso
    bMRanks
    lyubeznikMatching 
    criticalLyubeznikCells
    trimmedRanks
///


-------------------
-- Bridge Trimmed Lyubeznik Documentation
-------------------

doc ///
Node 
Key
    possibleTrimmedEdges 
    (possibleTrimmedEdges, Sequence, Sequence)  
Headline
    prints all edges of a Barile-Macchia matching with respect to $S2$ of the Lyubeznik complex of a monomial ideal $I$ with respect to a total
    order $S1$ on $G(I)$ before Step 3) of Algorithm 2.6 in [CK]
Usage
    possibleTrimmedEdges(S1,S2)
Inputs
    S1: Sequence
    	a sequence of monomials
	a total order on a set of monomials
    S2: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Recall that the possible edges of the Barile-Macchia matching of $I$ with respect to $S1$ are directed edges of $G$, the
      directed graph obtained from the Taylor complex of $I$. Instead of the Taylor complex, one can apply the Barile-Macchia 
      algorithm (Algorithm 2.6 in [CK]) to any simplicial complex that supports a free resolution of $I$ by [BW].
      
      Instead of the Taylor complex, we consider the directed graph $G_L$ that is obtained from the Lyubeznik complex of 
      $I$ with respect to a total order $S1$ on $G(I)$. The collection of directed edges in $G_L$ that are produced after 
      Steps 1) and 2) of Algorithm 2.6 in [CK] is called the possible edges of the Barile-Macchia matching of the Lyubeznik complex
      of $I$ with respect to $S2$. 
      
      Given total orders $S1$ and $S2$ on $G(I)$ for a monomial ideal $I$, this function returns the list of potential edges of 
      the Barile-Macchia matching with respect to $S2$ of the Lyubeznik complex of $I$ with respect to $S1$. 
      
  Example
      R=QQ[a,b,c,d]
      S1 = (c*d, b*c, a*b, a*d);
      S2 = (a*d, c*d, b*c, a*b);
      possibleTrimmedEdges(S1,S2)
      
References
    [CK] T. Chau and S. Kara, Barile-Macchia Resolutions. Preprint, @arXiv "2211.04640"@ (2022).
    [BW] E. Batzies and V. Welker, Discrete Morse theory for cellular resolutions, J. Reine Angew. Math. 543 (2002).
      
SeeAlso
    possibleEdges
    trimmedMatching
///


doc ///
Node 
Key
    trimmedMatching 
    (trimmedMatching, Sequence, Sequence)  
Headline
    prints all edges of a Barile-Macchia matching with respect to $S2$ of the Lyubeznik complex of monomial ideal $I$ with respect to a total
    order $S1$ on $G(I)$
Usage
    trimmedMatching(S1,S2)
Inputs
     S1: Sequence
    	a sequence of monomials
	a total order on a set of monomials
    S2: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $L$ be the Lyubeznik complex of a monomial ideal with respect to a total order $S1$ on $G(I)$. One can find the Barile-Macchia matching 
	of $L$ with respect to a given total order $S2$ on $G(I)$.
      
      Given total orders $S1$ and $S2$ on $G(I)$ for a monomial ideal $I$, this function returns the Barile-Macchia matching 
      with respect to $S2$ of the Lyubeznik complex of $I$ with respect to $S1$.
      
  Example
      R=QQ[a,b,c,d]
      S1 = (c*d, b*c, a*b, a*d);
      S2 = (a*d, c*d, b*c, a*b);
      trimmedMatching(S1,S2) 
       
SeeAlso
    possibleTrimmedEdges
    bMMatching
    lyubeznikMatching
///

doc ///
Node 
Key
    criticalTrimmedCells 
    (criticalTrimmedCells, Sequence, Sequence)  
Headline
    prints all critical cells of the Lyubeznik complex of a monomial ideal generated by the given sequence with respect to its Barile-Macchia matching
Usage
    criticalTrimmedCells(S1,S2)
Inputs
     S1: Sequence
    	a sequence of monomials
	a total order on a set of monomials
    S2: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Let $I$ be the monomial ideal and $S1$ and $S2$ be two total orders on $G(I)$. A subset of a minimal generating set of $I$ is called 
      A-critical if it does not appear in A, a homogeneous acyclic matching of $I$ with respect to $S1$ (or $S2$).
      
      Let $L$ be the Lyubeznik complex of a monomial ideal $I$ with respect to a total order $S1$ on $G(I)$.
      
      Given a monomial ideal $I$ and two total orders $S1$ and $S2$ on $G(I)$, this function returns a list of Barile-Macchia critical 
      subsets with respect to $S2$ of the Lyubeznik complex $L$ with respect to $S1$.
      
  Example
      R=QQ[a,b,c,d];
      S1 = (c*d, b*c, a*b, a*d);
      S2 = (a*d, c*d, b*c, a*b);
      criticalTrimmedCells(S1,S2) 
      
SeeAlso
    trimmedMatching
    criticalBMCells
    criticalLyubeznikCells
///

doc ///
Node 
Key
    trimmedRanks 
    (trimmedRanks, Sequence, Sequence)  
Headline
    prints the ranks of the trimmed Lyubeznik resolution (via Barile-Macchia matching with respect to $S2$) of a monomial ideal $I$ with respect 
    to a total order $S1$ on $G(I)$  
Usage
    trimmedRanks(S1,S2)
Inputs
     S1: Sequence
    	a sequence of monomials
	a total order on a set of monomials
    S2: Sequence
    	a sequence of monomials
	a total order on a set of monomials
Outputs
    :List
Description
  Text
      Given total orders $S1$ and $S2$ on $G(I)$ for a monomial ideal $I$, this function returns the ranks of the free modules of the 
      free resolution obtained by trimming the Lyubeznik resolution of $R/I$ with respect to $S1$ by using the Barile-Macchia matching with 
      respect to $S2$. The output is a list of numbers where the $i^{th}$ number in the list is the rank of the free module at $i^{th}$ 
      homological degree.
      
      
  Example
     R=QQ[a,b,c,d];
     S1 = (c*d, b*c, a*b, a*d);
     S2 = (a*d, c*d, b*c, a*b);
     trimmedRanks(S1,S2)
     
SeeAlso
    bMRanks
    lyubeznikRanks
    criticalTrimmedCells 
///

-------------------
-- Tests
-------------------


-- Tests taylorCell
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    I = ideal S;
    taylorCell(I,2)
///

-- Tests allTaylorCells
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    I = ideal S;
    allTaylorCells(I)
///

-- Tests bridge
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    I = ideal S;
    T=taylorCell(I,3);
    bridge(T_0)
///

-- Tests smallestBridge
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    I = ideal S;
    T=taylorCell(I,3);
    smallestBridge(T_0,S)
///

-- Tests possibleEdgesWithPositions
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    possibleEdgesWithPositions(S)
///

-- Tests possibleEdges
TEST ///
    R=QQ[a,b,c,d];
    S = (c*d, b*c, a*b, a*d);
    possibleEdges(S)
///

-- Tests bMMatching
TEST ///
   R=QQ[a,b,c,d];
   S = (c*d, b*c, a*b, a*d);
   bMMatching(S)
///


-- Tests isBridgeFriendly
TEST ///
   R=QQ[a,b,c,d];
   S = (c*d, b*c, a*b, a*d);
   isBridgeFriendly(S)
///

-- Tests friendlyStep
TEST ///
   R=QQ[a,b,c,d];
   S = (c*d, b*c, a*b, a*d);
   friendlyStep(S)
///

-- Tests bridgeFriendlyList
TEST ///
   R=QQ[a,b,c,d];
   I=ideal(a*b,b*c,c*a);
   bridgeFriendlyList(I)
///

-- Tests criticalBMCells
TEST ///
   R=QQ[a,b,c,d];
   S = (c*d, b*c, a*b, a*d);
   criticalBMCells(S)
///

-- Tests bMRanks
TEST ///
   R=QQ[a,b,c,d];
   S = (c*d, b*c, a*b, a*d);
   bMRanks(S)
///

-- Tests lyubeznikBridge
TEST ///
   R=QQ[a,b,c,d];
   S = (a*b,b*c,c*d,d*a);
   L={b*c,c*d,d*a};
   lyubeznikBridge(L,S)
///

-- Tests lyubeznikMatching
TEST ///
  R=QQ[x_1..x_8];
  S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
  lyubeznikMatching(S)
///

-- Tests criticalLyubeznikCells
TEST ///
  R=QQ[x_1..x_8];
  S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
  criticalLyubeznikCells(S)
///


-- Tests lyubeznikRanks
TEST ///
  R=QQ[a,b,c,d];
  S = (c*d, b*c, a*b, a*d);
  lyubeznikRanks(S)
///


-- Tests possibleTrimmedEdges
TEST ///
  R=QQ[x_1..x_8];
  S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
  possibleTrimmedEdges(S,S)
///

-- Tests trimmedMatching
TEST ///
   R=QQ[x_1..x_8];
   S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
   trimmedMatching(S,S)
///


-- Tests criticalTrimmedCells
TEST ///
   R=QQ[x_1..x_8];
   S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
   criticalTrimmedCells(S,S)
///

-- Tests trimmedRanks
TEST ///
   R=QQ[x_1..x_8];
   S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4);
   trimmedRanks(S,S)
///



end--
