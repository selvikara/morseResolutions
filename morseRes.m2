--
--Function 1: prints all Taylor symbols of I with cardinality k
--

taylorSym = method(TypicalValue => List)
taylorSym(Ideal,ZZ) := List => (I,k)->(
    select(subsets flatten entries gens I, i-> #i==k)
    )

--Test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
taylorSym(I,2)

--
--Function 2: prints all Taylor symbols of I
--
allTaylorSym = method(TypicalValue => List) 
allTaylorSym(Ideal):= List => I->(
    M= flatten entries gens I;
    L=for k from 0 to #M-1 list taylorSym(I,#M-k);
    L
    )

--Test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
allTaylorSym(I)


--
--Function 3: prints all bridges of a given Taylor symbol (as a list)
--

bridge = method(TypicalValue => List)
bridge(List) := List => L ->(
    if #L<3 then print "Taylor symbol is too small to contain a bridge" L else select(L, i -> lcm L == lcm delete(i,L))
     )

--Test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
T=taylorSym(I,3)
bridge(T_0)

R=QQ[a,b,c,d,e]
S = (c*d, b*c, a*b, a*d);
I = ideal S
L={a*b,a*d,a*e}
bridge(L)  

--
--Function 4: prints the smallest bridge of a given Taylor symbol L (a list) with respect to 
--a total order S (a sequence where the elements are from smallest to largest)
--
smallestBridge = method(TypicalValue => RingElement)
smallestBridge(List, Sequence) := RingElement => (L, S) ->(
    if bridge L=!={} then (
	sortB = select(S, i-> member(i,bridge L)); --select returns a list in the same order as the input list
    	sortB_0
	)
    else print "no bridges exist"
    )


--Test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
T=taylorSym(I,3)
smallestBridge(T_0,S)


--
--Function 5: prints all edges before we remove the ones involving symbols
-- that are potential type-2 but not type 2.
--

possibleEdges = method(Dispatch => Thing)
possibleEdges(Sequence) := List => S -> (
    I = ideal S;
    Sigma = drop(allTaylorSym I, -2); --drops the Taylor symbols of length 1 and 2
    Omega = flatten drop(allTaylorSym I, -2);
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
    )

--Test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
possibleEdges(S)

--
--Function 6: prints out the bridge matching
-- ouput is {list of edges (ordered pairs) in the bridge matching, Boolean check if bridge friendly}


BridgeMatching = method(Dispatch => Thing)
BridgeMatching(Sequence) := List => S -> (
    A = possibleEdges S;
    groupedA = hashTable apply(A, i->(i_2, select(A,j->j_2==i_2)));
    minA = applyValues(groupedA, i-> min i);
    Bridge = apply(values minA, i->drop(i,1));
    {Bridge, #A==#Bridge}
    )


--test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
I = ideal S
BridgeMatching(S)



--
--Function 7: checks if I is bridge friendly for any total ordering.
-- prints out the total orders where I is bridge friendly as the first components 
-- and the corresponding bridge matching 
-- 

BridgeFriendly = method(TypicalValue => List)
BridgeFriendly(Ideal) := List => I -> (
    -- take all permutations of S, find BridgeMatching, check if second component is true for any of them
    orderings = permutations flatten entries gens I;
    Bridges = apply(orderings, i-> {i}|BridgeMatching(toSequence i)); --output is {S, M, Bridge friendly?}
    friendlies = select(Bridges, i -> i_2); --i_2 is Boolean so this will only select true guys
    apply(friendlies, i->drop(i,-1))
    )
    
--test 
R=QQ[a,b,c,d]
 I=ideal(a*b,b*c,c*a)
 BridgeFriendly(I)
 --this ideal is bridge friendly wrt all total orders

 
    
--   	
--Function 8: prints all critical symbols 
-- these are all Taylor symbols that are neither a source nor target in the bridge matching
-- output is {list of critical symbols, grouped based on cardinality}
--

criticalSymbols = method(Dispatch => Thing)
criticalSymbols(Sequence) := List => S -> (
    I = ideal S;
    crit = allTaylorSym I;
    n = #crit;
    nonCrit = BridgeMatching(S);
    for i from 0 to #nonCrit_0-1  do(
        k = #nonCrit_0_i_0;
        sigma1 = nonCrit_0_i_0;
        sigma2 = nonCrit_0_i_1;   
        crit1 = crit_(n-k);
        crit2 = crit_(n-k+1);
        crit1 = delete(sigma1, crit1);
        crit2 = delete(sigma2, crit2);
        crit = replace(n-k, crit1, crit);
        crit = replace(n-k+1, crit2, crit);
    );
    crit
    )

--
--Function 9: second version
-- 

criticalSymbols = method(Dispatch => Thing)
criticalSymbols(Sequence) := List => S -> (
    I = ideal S;
    BM=BridgeMatching(S);	
    Z=select(splice BM_0, m -> #m>1);
    Omega = flatten drop(allTaylorSym I, -1);
    C=select(Omega, i-> not member(i,Z));
    A= set{taylorSym(I,1)}+set{C};
    flatten toList A 
    )

--test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
criticalSymbols(S)


--   	
--Function 10: prints the ranks of a bridge resolution wrt S 
--output : list of ranks of the bridge resolution
     
bridgeRank = method(Dispatch => Thing)
bridgeRank(Sequence) := List => S -> (
    crit = criticalSymbols(S);
    n = #crit;
    rankList = {};
    for i from 0 to (n-1) do (
        rankList = append(rankList, #crit_(n-i-1) );
        );
    rankList
    )


--test
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d);
bridgeRank(S)

--
-- Function 10, version 2
--

--step 1: partial rank

PartialRank= method(TypicalValue => List)
PartialRank(Sequence,ZZ) := List => (S,k)->(
    C = criticalSymbols(S);
    #select(C, i-> #i==k)
    )

--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
PartialRank(S,3)
PartialRank(S,2)
PartialRank(S,1)

--step 2: lists all partial ranks
--- the order is reversed in this version of Function 10

BridgeRank = method(Dispatch => Thing)
BridgeRank(Sequence) := List => S -> (
    L=for k from 0 to #S-1 list PartialRank(S,#S-k);
    L
    )


--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
BridgeRank(S)
