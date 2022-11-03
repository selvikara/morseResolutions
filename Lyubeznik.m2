--Lyubeznik resolution--

--main functions needed from morseRes.m2--


taylorSym = method(TypicalValue => List)
taylorSym(Ideal,ZZ) := List => (I,k)->(
    select(subsets flatten entries gens I, i-> #i==k)
    )

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
taylorSym(I,2)
allTaylorSym(I)

--
--Function 1. Lyubeznik bridge function 
--

bridgeLyubeznik = method(TypicalValue => List)
bridgeLyubeznik(List,Sequence) := List => (L,S) ->(
    if #L<3 then print "Taylor symbol is too small to contain a Lyubeznik
bridge"
    else A={};
for i from 0 to #S-1 do(
    B=S_i;
    L=delete(B,L);
    if ( #L>0 and lcm L // B !=0) then A=append(A,B);
    );
A
)

--
--Function 2. Smallest Lyubeznik bridge function 
--


smallestLyubeznikBridge = method(TypicalValue => RingElement)
smallestLyubeznikBridge(List, Sequence) := RingElement => (L, S) ->(
    if bridgeLyubeznik(L,S)=!={} then (
    B=bridgeLyubeznik(L,S);
    B_0
    )
    else print "no Lyubeznik bridges exist"
    )


--example 1
R=QQ[a,b,c,d]
S = (a*b,b*c,c*d,d*a)
L={b*c,c*d,d*a}
bridgeLyubeznik(L,S) --output must be {a*b}
smallestLyubeznikBridge(L,S) --output must be a*b

--example 2
R=QQ[a,b,c,d]
S = (a*b,b*c,c*d,d*a)
L={a*b,b*c,c*d,d*a}
bridgeLyubeznik(L,S) --output must be {a*b}
smallestLyubeznikBridge(L,S) --output must be a*b

--example 3
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4}
bridgeLyubeznik(L,S) --output must be {x_1*x_2*x_5}
smallestLyubeznikBridge(L,S) --output must be x_1*x_2*x_5

--example 4
R=QQ[a,b,c,d,e]
S = (a*b,b*c,c*d,d*e)
L={a*b,b*c,c*d,d*e}
bridgeLyubeznik(L,S) -- output must be the empty set
smallestLyubeznikBridge(L,S) -- output must be "No Lyubeznik bridge exists"

--example 5
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6}
bridgeLyubeznik(L,S) -- output must be the empty set
smallestLyubeznikBridge(L,S) -- output must be "No Lyubeznik bridge exists"
 


--
-- Function 3. LyubeznikMatching
--

LyubeznikMatching = method(Dispatch => Thing)
LyubeznikMatching(Sequence) := List => S -> (
    I = ideal S;
    Omega = flatten drop(allTaylorSym I, -2);
    LMatching={};
    while #Omega >0 do(
    	sigma = Omega_0;
    	if bridgeLyubeznik(sigma,S) =!= {} then(
	    	sb = smallestLyubeznikBridge(sigma, S);
	    	sigmaMinusSb = delete(sb, sigma);
	    	LMatching = append(LMatching, (sigma, sigmaMinusSb));
	    	Omega = delete(sigma, Omega);
	    	Omega = delete(sigmaMinusSb, Omega);
	    	)
    	    else Omega = delete(sigma, Omega);
    );
    LMatching
    )



--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
LyubeznikMatching(S)


--test2--
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4} 
LyubeznikMatching(S)
 
 
--test 3
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6} 
LyubeznikMatching(S)

--
-- Function 4. Critical Lyubeznik Symbols
--

criticalLyubeznikSymbols = method(Dispatch => Thing)
criticalLyubeznikSymbols(Sequence) := List => S -> (
    I = ideal S;
    LM=LyubeznikMatching(S);	
    Z=select(splice LM, m -> #m>1);
    Omega = flatten drop(allTaylorSym I, -1);
    C=select(Omega, i-> not member(i,Z));
    critLyuSyms= set{taylorSym(I,1)}+set{C};
    flatten toList critLyuSyms 
    )

--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
criticalLyubeznikSymbols(S)


--test2--

R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4} 	
criticalLyubeznikSymbols(S)
 
 
--test 3
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6} 
criticalLyubeznikSymbols(S)

--
-- Function 5. Lyubeznik rank
---

--step 1: partial Lyubeznik

PartialLyubeznikRank= method(TypicalValue => List)
PartialLyubeznikRank(Sequence,ZZ) := List => (S,k)->(
    C = criticalLyubeznikSymbols(S);
    #select(C, i-> #i==k)
    )

--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
PartialLyubeznikRank(S,2)

--step 2: Lyubeznik

LyubeznikRank = method(Dispatch => Thing)
LyubeznikRank(Sequence) := List => S -> (
    L=for k from 0 to #S-1 list PartialLyubeznikRank(S,#S-k);
    L
    )


--test 1---
R=QQ[a,b,c,d]
S = (c*d, b*c, a*b, a*d)
criticalLyubeznikSymbols(S)
LyubeznikRank(S)


--test2--

R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4} 	
LyubeznikRank(S)
 
 
--test 3
R=QQ[x_1..x_8]
S=(x_7*x_8,x_2*x_3*x_8,x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6,x_1*x_2*x_3*x_4)
L= {x_1*x_2*x_7,x_1*x_2*x_5,x_2*x_3*x_5*x_6} 
LyubeznikRank(S)
