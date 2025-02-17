#source: Micha\"el Mignard, Peter Schauenburg, https://arxiv.org/abs/1708.06538
LoadPackage("hapco");


InstallMethod( OneMutable,true,[IsCcElement],0,c -> One(InCcGroup(c)) );




ComplementIntMatWithTransforms:=function( full,sub )
local F, S, M, r, T, c, R;
  F := BaseIntMat( full );
  if IsEmpty( sub ) or IsZero( sub ) then
    return rec( complement := F, sub := [], moduli := [] );
  fi;
  S := BaseIntersectionIntMats( F, sub );
  if S <> BaseIntMat( sub ) then
    Error( "sub must be submodule of full" );
  fi;
  # find T such that BaseIntMat(T*F) = S
  M := Concatenation( F, S );
  T := NormalFormIntMat( M, 4 ).rowtrans^-1;
  T := T{[Length(F)+1..Length(T)]}{[1..Length(F)]};
  c := NormalFormIntMat(T*F,6)!.rowtrans;

  # r.rowtrans * T * F = r.normal * r.coltrans^-1 * F
  r := NormalFormIntMat( T, 13 );
  M := r.coltrans^-1 * F;
  R := rec( complement := BaseIntMat( M{[1+r.rank..Length(M)]} ),
            sub := r.rowtrans * T * F,
            moduli := List( [1..r.rank], i -> r.normal[i][i] ) ,
	    fulltrans := r.coltrans^(-1),
	    subtrans := r!.rowtrans*c^(-1));
  return R;
end;


#& cohomology #&

UniversalCoefficientsTheorem:=function(K,n)
local ZZ,     # a basis for Z_n(K)
      B,      # a basis for B_n(K)
      r,      # the ABT for Z_n(K) and B_n(K)
      C,      # the matrix C
      D,      # the list of the invariant factors
      m,      # the exponent of the H_n(K)
      homlist,# a "basis" for Hom(H_n(K),Z/mZ)
      r2, R1,C1,
              # the different variables implicated
              # in the ABT for K_n and Z_n(K)
		
      I,      # the matrix I
      cocyclelist;
              # a "basis" for H^n(K,C^*)


	
ZZ:=NullspaceIntMat(TransposedMat(
                BoundaryMatrix(K,n)));
if not Size(ZZ)>0 then return 
	rec(	complex:=K,
		cyclebasis:=ZZ,
		cycletrans:=[],
		hombasis := [],
		cocyclebasis := [],
		torsion := [1],
		exponent := 1,
		lift:=[]
	);
fi;
B:=BaseIntMat(TransposedMat(
                 BoundaryMatrix(K,n+1)));
r:=ComplementIntMatWithTransforms(ZZ,B);
C:=r!.fulltrans;
D:=r!.moduli;
m:=D[Size(D)];
homlist:=[];
List(Filtered(D,x->not x=1),x->
	ListWithIdenticalEntries(Size(ZZ),0));
for i in [1..Size(D)] do
	if D[i]=1 then continue;fi;
	hom:=ListWithIdenticalEntries(Size(ZZ),0);
	hom[i]:=m/D[i];
	Add(homlist,hom);
od;
homlist:=List(homlist,x->((C^(-1))*x) mod m);

r2:=ComplementIntMatWithTransforms(
              IdentityMat(K!.dimension(3)),ZZ);
C1:=r2!.subtrans;
R1:=r2!.fulltrans;

I:=Concatenation(IdentityMat(Size(ZZ)),
     NullMat(K!.dimension(n)-Size(ZZ),Size(ZZ)));
cocyclelist:=List(homlist,x->(R1^(-1)*(I*(C1*x))) 
                     mod m);
	
return( rec(
	complex:=K,
	cyclebasis:=ZZ,
	cycletrans:=C,
	hombasis := homlist,
	cocyclebasis := cocyclelist,
	torsion := Filtered(D,x->not x=1),
	exponent := m,
	lift:=R1^(-1)*I*C1
		)
	);
end;


#& end #&


#& order #&

CocycleOrder:=function(f,m)
	local list;
	list:=List(Filtered(f,x->not x=0),
                   x->m/Gcd(x,m));
	if list=[] 
		then return 1;
		else return Maximum(list);
	fi;
end;    

#& end #&   

#& functoriality #&

GroupCohomologyFunctor:=function(K1,K2,phi,n)
local 	UCT1, 	# UCT for K1
	m1, 	# the exponent of H_n(K1)
	Z1,	# the adapted basis of Z_n(K1)
	UCT2, 	# UCT for K2
	m2, 	# the exponent of H_n(K2)
	Z2,	# the adapted basis of Z_n(K2)
	p, 	# p=lcm(m1,m2)
	F, 	# the matrix F
	hphi; 	# the morphism H_n(phi)
		

UCT1:=UniversalCoefficientsTheorem(K1,n);;
m1:=UCT1!.exponent;;
Z1:=UCT1!.cyclebasis;
s:=NormalFormIntMat(Z1,13);
UCT2:=UniversalCoefficientsTheorem(K2,n);;
m2:=UCT2!.exponent;;
Z2:=UCT2!.cyclebasis;
F:=List(Z1,
	x->SolutionIntMat(Z2,phi!.mapping(x,n)));;
p:=Lcm(m1,m2);;

hphi:=function(f)
	return ((F*(m1*f))/m2) mod m1;
end;
return rec(
	matrix:=F,
	mapping:=hphi,
	p:=p,
	m1:=m1,
	m2:=m2);
end;

#& end #&


#& proj #&

ProjectiveCharacters:=function(G,alpha,o)
local A,r,Ga,Gaa,ire,t,lift,testpro;

# we represent the cyclic group as a G-Outer group

A:=GOuterGroup();
SetActingGroup(A,G);
if o=1 then
    SetActedGroup(A,GroupByGenerators(
	[One(CyclicGroup(o))]));
    else
        SetActedGroup(A,CyclicGroup(o));
fi;
SetOuterAction(A,function(g,x) return x; end);

# we represent the cocycle f as a 
# standard 2-cocycle in HAP 

r:=Standard2Cocycle();
SetActingGroup(r,A!.ActingGroup);
SetMapping(r,function(x,y) return 
	(A!.ActedGroup.1)^alpha(x,y);
	end);
SetModule(r,A);


# now, we construct the extension of G by A along r
# we also give its character table

Ga:=CcGroup(A,r);
Gaa:=UnderlyingGroup(Ga);
ire:=Irr(Gaa);

# we give the element in Gaa that corresponds to 
# the generators of the cyclic group, and a 
# section of the epi of Gaa on G


t:=CcElement(FamilyObj(One(Ga)),GeneratorsOfGroup(
   Ga!.Fibre)[1],One(Ga!.Base),InCcGroup(One(Ga)));
lift:=function(g)
      return CcElement(FamilyObj(One(Ga)),
	One(Ga!.Fibre),g,InCcGroup(One(Ga)));
end;

# finally, we give the function that tests for a 
# charater of Gaa if it comes from a projective 
# character of G

testpro:=function(l)
	local list,chi;
	list:=[];
	for chi in l do
      		if t^chi/E(o)=(t^Size(Ga))^chi 
			then Add(list,chi); 
		fi;
	od;
	return list;
end;

return rec(
	Gaa:=Gaa,
	lift:=lift,
	table:=testpro(ire)
	);
end;

#& end #&


#& automorphisms #&

AutomorphismOrbits:=function(G,R,K,UCT)
local 	rcv,
	coho,
	aut,
	gens,
	autmat,
	orbits;

rcv:=function(x,n) 
     return List(x,y->ZmodnZObj(y,n));
     end;
coho:=NearAdditiveGroup(
      List(UCT!.hombasis,x->rcv(x,UCT!.exponent)));
aut:=AutomorphismGroup(G);
gens:=GeneratorsOfGroup(aut);
autmat:=List(
         gens,phi->TransposedMat(
          GroupCohomologyFunctor(
           K,K,TensorWithIntegers(
	    EquivariantChainMap(R,R,phi)),
           3)!.matrix));
autmat:=List(
         autmat,x->List(
                    x,y->rcv(y,UCT!.exponent)));
orbits:=OrbitsDomain(aut,coho,gens,autmat);
return List(orbits,x->List(x,y->List(
                                 y,z->Int(z))));
end;

#& end #&


#& exponent #&

ExponentOfPFC:=function(G,R,K,UCT,hom)
local 	H,
	R2,
	K2,
	UCT2,
	m,
	phi,
	chainmap,
	res,
	list;

list:=[];
for H in Filtered(AllSubgroups(G),
		IsCyclic and IsNonTrivial) do
R2:=ResolutionFiniteGroup(H,4);
K2:=TensorWithIntegers(R2);
UCT2:=UniversalCoefficientsTheorem(K2,3);
m:=UCT2!.exponent;
phi:=GroupHomomorphismByFunction(H,G,h->h);
chainmap:=TensorWithIntegers(
	EquivariantChainMap(R2,R,phi));
res:=GroupCohomologyFunctor(
      K2,UCT!.complex,chainmap,3)!.mapping(
		hom);
Add(list,[Size(H),CocycleOrder(res,m)]);
od;
return Lcm(List(list,x->x[1]*x[2]));
end;

#& end #&




#& pi #&

ValuesOfPiSymbols:=function(G,R,K,UCT,x,f)
local n,e,o,list1,list2,m,i,j;
n:=UCT!.exponent;
e:=Exponent(G);
o:=Order(x);
list1:=[1];
for m in [1..o] do
Add(list2,
 factors[Size(list2)]*E(n)^f(x,x^(m-1),x));
od;
list2:=[1];
for j in [1..e] do
Add(list2,(list1[o+1]^QuoInt(j,o))
          *(list1[RemInt(j,o)+1]));
od;
return list2;
end;


#& end #&

#& twist #&

Twist:=function (class, C, lift, chi)
	return lift( class ) ^ chi / 
		lift( class ^ Size( C ) ) ^ chi;
end;



#& end #&


alphag:=function(g)
local f,x,y;
return function(f)
	return function(x,y)
    		return f(x,y,g)-f(x,y*g*y^(-1),y)+f(x*y*g*y^(-1)*x^(-1),x,y);end;
	end;
end;

#& indicator #&

FSIforDoubles:=function(
	G, 
	f, 
	class, 
	proj, i, 
	n, 
	listG, 
	pivalues, 
	m
	)
local e,C,Gaa,lift,chi,sum,x;
e:=Exponent(G);
C:=Centralizer(G,class);
Gaa:=proj!.Gaa;
lift:=proj!.lift;
chi:=proj!.table[i];
sum:=0;
for x in G do    
	if (class*x)^m=x^m then 
sum:=sum + E(n)^alphag(x^m)(f)(class,x)*
((pivalues[Position(listG,class*x)][e+1]/
pivalues[Position(listG,x)][e+1])^QuoInt(m,e))*
(pivalues[Position(listG,class*x)][RemInt(m,e)+1]/
pivalues[Position(listG,x)][RemInt(m,e)+1])*
lift((x^m))^chi;
        fi;
od;
return sum/Size(C);
end;


#& end #&





GaugeInvariants:=function(G)
    local 	R,
		K,
		UCT,
		n,
		hom,
		lift,
		orbits,
		representatives,
		o,
		listG,
		list,
		j,
		h,
		omega,
		f,
		exp,
		conj,
		PC,
		pivalues,
		FSlist,
		l,
		indicators,
		twist,
		columns;
	R:=ResolutionFiniteGroup(G,4);
	K:=TensorWithIntegers(R);
    	UCT:=UniversalCoefficientsTheorem(K,3);
    	Print("Cohomology done\n\n");
    	n:=UCT!.exponent;
	hombasis:=UCT!.hombasis;
    	lift:=UCT!.lift;
    	orbits:=AutomorphismOrbits(G,R,K,UCT);
    	representatives:=List([1..Size(orbits)],i->(lift*orbits[i][1])mod n);
    	Print("automorphism orbits done\n\n");
	listG:=Enumerator(G);
    	list:=[];
    	for j in [1..Size(representatives)] do
		h:=orbits[j][1];
        	omega:=representatives[j];
        	f:=StandardCocycle(R,omega,3,n);
        	exp:=ExponentOfPFC(G,R,K,UCT,h);
		conj:=List(ConjugacyClasses(G),x->Representative(x));
        	PC:=List(conj,g->ProjectiveCharacters(Centralizer(G,g),alphag(g)(f),n));
        	pivalues:=List(listG,x->ValuesOfPiSymbols(G,R,K,UCT,x,f));
		FSlist:=DivisorsInt(exp);l:=Size(FSlist);FSlist:=Concatenation([0],FSlist{[1..l-1]});
        	indicators:=Concatenation(List([1..Size(PC)],i->List([1..Size(PC[i]!.table)],j->List(FSlist,m->FSIforDoubles(G,f,conj[i],PC[i],j,n,listG,pivalues,m)))));
        	twist:=Concatenation(List([1..Size(PC)],i->List([1..Size(PC[i]!.table)],j->Twist(conj[i],Centralizer(G,conj[i]),PC[i]!.lift,PC[i]!.table[j]))));
        	SortParallel(indicators,twist);
        	columns:=Size(FSlist);
        	Add(list,[representatives[j],FSlist,Collected(List([1..Size(indicators)],i->Concatenation(List([1..columns],j->indicators[i][j]),[twist[i]])))]);
		Print(String(representatives[j]),"done\n\n");
    	od;
    	return rec( UCT:=UCT, orbits:=orbits, representatives:=representatives, Table:=list);
end;






#& ptindicators #&
		

FSIforPFC:=function(G,omega)
local R,K,UCT,n,f,listG,pivalues,list,result,nu,g,m;
R:=ResolutionFiniteGroup(G,4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K,3);
n:=UCT!.exponent;
f:=StandardCocycle(R,omega,3,n);
listG:=Enumerator(G);
pivalues:=List(listG,x->
               ValuesOfPiSymbols(G,R,K,UCT,x,f));
nu:=function(G,f,x,m)
local o;
if x^m=One(G) then
  o:=Order(x);
  return (pivalues[Position(listG,x)][o+1]
           ^(QuoInt(-m,o)-1))
    *pivalues[Position(listG,x)][o-RemInt(-m,o)+1];
else return 0;
fi;
end;
result:=[];
for g in G do
  list:=[];
  for m in [0..ExponentOfPFC(G,R,K,UCT,
            (UCT!.cyclebasis*omega) mod n)-1] do
    Add(list,nu(G,f,g,m));
  od;
  Add(result,list);
od;
return result;
end;

#& end #&

#& adaptation #&

d:=function(eta)
return
  function(g,h,k) 
   return eta(h,k)-eta(g*h,k)+eta(g,h*k)-eta(g,h);
  end;
end;

moduloQ:=function(G,N,Q,g)
local p;
for p in Q do
 if p^(-1)*g in N then return [p,p^(-1)*g]; fi;
od;
end;

IsAdaptatedCocycle:=function(G,R,N,omega)
    local e,g,h,k,bool;
    e:=R!.exponent;
    bool:=true;
    for g in G do
        for h in G do
            for k in N do
                bool:=(omega(g,h,k)=0 mod e);
                if bool=false 
                then 
                    break;
                fi;
            od;
        od;
    od;
    return bool;
end;



FirstStep:=function(G,R,N,omega)
local Q,eta_1,omega_0;
Q:=List(RightCosets(G,N),x->Representative(x));
eta_1:=function(g,h)
 return omega(moduloQ(G,N,Q,g)[1],
         moduloQ(G,N,Q,g)[2],moduloQ(G,N,Q,h)[2]);
end;
omega_0:=function(g,h,k) 
 return omega(g,h,k)+d(eta_1)(g,h,k); 
end;
return omega_0;
end;

SecondStep:=function(G,R,N,omega_0)
local Q,eta_2,omega_1;
Q:=List(RightCosets(G,N),x->Representative(x));
eta_2:=function(g,h) 
 return 
  -(omega_0(g,moduloQ(G,N,Q,h)[1],
            moduloQ(G,N,Q,h)[2]))
  +omega_0(moduloQ(G,N,Q,g)[1],moduloQ(G,N,Q,g)[2],
   moduloQ(G,N,Q,h)[1]);
 end;
omega_1:=function(g,h,k) 
 return omega_0(g,h,k)+d(eta_2)(g,h,k);
end;
return omega_1;
end;

#& end #&




#& gtindicators #&

FSIforAGT:=function(G,N,omega)
local R,K,UCT,hom,FSexp,f,omega_0,omega_1,
      cosets,PC,list,result,i,j,nu,m;
R:=ResolutionFiniteGroup(G,4);
K:=TensorWithIntegers(R);
UCT:=UniversalCoefficientsTheorem(K,3);
hom:=(UCT!.cyclebasis*omega) mod UCT!.exponent;
FSexp:=ExponentOfPFC(G,R,K,UCT,hom);
f:=StandardCocycle(R,omega,3,UCT!.exponent);
omega_0:=FirstStep(G,R,N,f);
omega_1:=SecondStep(G,R,N,omega_0);
cosets:=DoubleCosets(G,N,N);
PC:=List(cosets,g->ProjectiveCharacters(
  Intersection(N,N^(Representative(g)^(-1))),
  function(x,y)
   return omega_1(x,y,Representative(g));
  end,
  UCT!.exponent));
nu:=function(G,UCT,N,f,class,list,i,m)
 local x,sum,S,Pf,lift,chi,listG,pivalues,r,o;
 S:=Intersection(N,
     N^(Representative(class)^(-1)));
 Gaa:=list!.Gaa;
 lift:=list!.lift;
 chi:=list!.table[i];
 listG:-Enumerator(G);
 pivalues:=List(listG,x->
            ValuesOfPiSymbols(G,R,K,UCT,x,f));
 sum:=0;
 for r in N do
  if (Representative(class)*r)^m in S 
  then 
   o:=Order(Representative(class)*r);
   sum:=sum 
    +(pivalues[Position(listG,
                Representative(class)*r)][o+1]
      ^(QuoInt(-m,o)-1))
    *pivalues[Position(listG,
                       Representative(class)*r)
      [o+RemInt(-m,o)+1]
    *lift(((Representative(class)*r)^(-m)))^chi; 
  fi;
 od;
return sum/Size(S);
end;
result:=[];
for i  in [1..Size(PC)]  do
 for j in [1..Size(PC[i]!.table)] do
  list:=[];
  for m in [0..FSexp-1] do
   Add(list,
       nu(G,UCT,N,omega_1,cosets[i],PC[i],j,m));
  od;
  Add(result,list);
 od;
od;
return result;
end;
#& end #&
