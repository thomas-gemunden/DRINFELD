#(C) Graham Ellis, 2005-2006
#
# A-7 perf-5e (issue #284): patched AddFreeWords using a positional-pool
# scheme. The original linear `Position(w2, [-x[1], x[2]])` makes
# AddFreeWords cost O(|w1| * |w2|). The replacement is O(|w1| + |w2|).
#
# Algorithm (mirrors perf-5c's _AddFreeWordsFast, see
# extraspecial_orbifolds/scripts/solver/snf_wrapper.g for the rationale):
#
#   1. Branch the same way HAP does: pick the SHORTER input as `w`
#      (lookup target), longer as `v` (iteration). This preserves HAP's
#      output ordering rules.
#   2. For inputs with `|w| < 24`, fall through to the original linear
#      path - PosPlist on small lists beats interpreted dict overhead.
#   3. Otherwise, build a positional pool `pool[key] := [positions in w]`
#      where `key := (g - 1) * stride + (c + D + 1)`. The pool is a
#      module-level plain list; module-level state is reused across calls
#      with O(|w|) cleanup via the `_touched` list.
#   4. For each x in v, look up `pool[encoded(-x[1], x[2])]` to find a
#      cancelling entry; zero both positions.
#   5. Collect surviving entries.
#
# Bit-identical output to the original AddFreeWords for any input:
#   * Same v/w selection by length (smaller -> w).
#   * Same cancellation rule (a single [-c,g] in v cancels the EARLIEST
#     [c,g] in w; both go to 0).
#   * Same final ordering: w's surviving entries (in their original
#     positions) followed by v's unmatched entries (in v's order).
#
# Verified by tests/test_perf5e_hap_addfreewords.g on 2300+ random + curated
# + Syzygy-derived inputs (after applying this patch).

#####################################################################
InstallGlobalFunction(Negate,
function(p);
return [-p[1],p[2]];
end);
#####################################################################

#####################################################################
InstallGlobalFunction(NegateWord,
function(b);
return List(b, x->[-x[1],x[2]]);
end);
#####################################################################

#####################################################################
InstallGlobalFunction(AlgebraicReduction,
function(arg)
local w,p,v,vv,vvv,vvvv,x,j,k,pos,pos2;

w:=arg[1];
if Length(arg)=2 then p:=arg[2]; else p:=0; fi;

if p=0  then

vv:=SSortedList(List(w,x->[AbsInt(x[1]),x[2]]));   #ADDED AUGUST 2022
if Length(vv) = Length(w) then return SortedList(w); fi;

#######################################
         v:=Collected(w);
         vv:=List(v,x->x[1]);
         vvv:=List(vv,x->[AbsInt(x[1]),x[2]]);
         vvv:=SSortedList(vvv);
         vvvv:=[];
         for x in vvv do
             pos:=Position(vv,x);
             pos2:=Position(vv,[-x[1],x[2]]);
             k:=0;
             if not pos=fail then k:=k+v[pos][2]; fi;
             if not pos2=fail then k:=k-v[pos2][2]; fi;
             if not k=0 then Append(vvvv,MultiplyWord(k,[x])); fi;
od;
return vvvv;
#######################################
fi;

        v:=Collected(w);
        Apply(v,x->[x[1],x[2] mod p]);
        Apply(v, x->MultiplyWord(x[2],[x[1]]));
        v:=Collected(Concatenation(v));
        Apply(v,x->[x[1],x[2] mod p]);
        Apply(v, x->MultiplyWord(x[2],[x[1]]));
        return Concatenation(v);

end);
#####################################################################


#####################################################################
InstallGlobalFunction(AlgebraicReduction_alt,
function(arg)
local ww,y,s,w,p,v,x,j,k,pos;

w:=arg[1];
if Length(arg)=2 then p:=arg[2]; else p:=0; fi;

if p= 0  then

        s:=SSortedList(w);
        Apply(s,x->[AbsInt(x[1]),x[2]]);
        s:=SSortedList(s);
        v:=[1..Length(s)]*0;
        for x in w do
        y:=[AbsInt(x[1]),x[2]];
        pos:=PositionSorted(s,y);
        v[pos]:=v[pos]+SignInt(x[1]);
        od;
        ww:=[];
        for j in [1..Length(v)] do
        if v[j]>0 then
        for k in [1..v[j]] do
        Add(ww,s[j]);
        od;
        else
        for k in [1..-v[j]] do
        Add(ww,[-s[j][1],s[j][2]]);
        od;
        fi;

        od;

        return ww;
fi;


	v:=Collected(w);
        Apply(v,x->[x[1],x[2] mod p]);
        Apply(v, x->MultiplyWord(x[2],[x[1]]));
        v:=Collected(Concatenation(v));
        Apply(v,x->[x[1],x[2] mod p]);
        Apply(v, x->MultiplyWord(x[2],[x[1]]));

	return Concatenation(v);


end);
#####################################################################


#####################################################################
# A-7 perf-5e (#284): O(|w1| + |w2|) AddFreeWords via positional pool.
#
# Module-level state (file scope; only this function reads/writes them):
#   HAP_AFW5e_pool       — a plain list, indexed by encoded (c, g) key,
#                          holding the ascending list of positions in w
#                          where the (c, g) pair occurs.
#   HAP_AFW5e_touched    — a plain list of keys we set during the current
#                          call, for O(|w|) reset at end-of-call.
#   HAP_AFW5e_D          — current max |c| supported; grows on demand.
#   HAP_AFW5e_G_max      — current max g supported; grows on demand.
#   HAP_AFW5e_stride     — = 2*D + 1 (cached for inner loop).
#   HAP_AFW5e_MIN_SMALL  — fall-through threshold for small inputs.
#
# The pool reset uses `Unbind(pool[key])` for each touched key, which is
# O(|touched|) instead of O(|pool|). The pool grows monotonically; reset
# happens only when capacity needs to bump.
#
# IMPORTANT: This patch ONLY gives a speedup over HAP's original linear
# scan when it is COMPILED via `compile.sh`. Without compilation, the
# extra GAP-interpreter work (pool dict + loop dispatch) outweighs the
# Position-loop savings, leading to a small regression (measured at
# m=3: ~22.8s caches wall patched-uncompiled vs ~19.5s HAP-original).
# After compilation the dict ops dispatch to GAP's compiled IsBound/Add
# /Unbind which run at C speed; the expected speedup is 4-10x on dense
# inputs.
#####################################################################

HAP_AFW5e_pool := [];;
HAP_AFW5e_touched := [];;
HAP_AFW5e_D := 64;;
HAP_AFW5e_G_max := 64;;
HAP_AFW5e_stride := 2 * HAP_AFW5e_D + 1;;
HAP_AFW5e_MIN_SMALL := 24;;

#####################################################################
InstallGlobalFunction(AddFreeWords,
function(arg)
local arg1, arg2, v, w, u, w_len, v_len, x, c, g, key, entry, neg_c,
      i, r, w2, pool, touched, stride, D, max_g, max_c, ic;

if Length(arg) < 2 then
    Error("AddFreeWords expects 2 arguments");
fi;
arg1 := arg[1];
arg2 := arg[2];

# Pick shorter as w (lookup target). Bit-identical to original branching.
if Length(arg2) < Length(arg1) then
    v := arg1; w := arg2;
else
    w := arg1; v := arg2;
fi;

w_len := Length(w);
v_len := Length(v);
# Empty-cases: original returns the non-empty arg as-is (no ShallowCopy).
# Match exactly to preserve any aliasing semantics callers may rely on.
if w_len = 0 then return v; fi;
if v_len = 0 then return w; fi;

# Small-input INLINED linear scan. HAP's compiled Position on a tight C
# loop already beats interpreted dict overhead for small w. Inlining
# (instead of delegating to a helper) avoids the extra function-call
# overhead on the hottest small-call path.
if w_len < HAP_AFW5e_MIN_SMALL then
    w2 := ShallowCopy(w);
    u := ShallowCopy(w);
    for x in v do
        r := Position(w2, [-x[1], x[2]]);
        if r = fail then
            Add(u, x);
        else
            u[r] := 0; w2[r] := 0;
        fi;
    od;
    return Filtered(u, i -> (not i = 0));
fi;

# Snapshot pool state.
pool := HAP_AFW5e_pool;
touched := HAP_AFW5e_touched;
stride := HAP_AFW5e_stride;
D := HAP_AFW5e_D;

# Build u as a mutable copy of w. Cancelled entries are zeroed.
u := ShallowCopy(w);

# Build positional pool. If any (c, g) overflows current bounds, grow
# the pool and bail to the inlined linear path for this call.
max_c := 0; max_g := 0;
for i in [1..w_len] do
    c := w[i][1];
    g := w[i][2];
    ic := AbsInt(c);
    if ic > max_c then max_c := ic; fi;
    if g > max_g then max_g := g; fi;
    if max_c > D or max_g > HAP_AFW5e_G_max then
        # Reset what we set so far.
        for key in touched do Unbind(pool[key]); od;
        HAP_AFW5e_touched := [];
        # Grow capacity. Stride changes -> pool is invalidated.
        if max_c > HAP_AFW5e_D then HAP_AFW5e_D := max_c; fi;
        if max_g > HAP_AFW5e_G_max then HAP_AFW5e_G_max := max_g; fi;
        HAP_AFW5e_stride := 2 * HAP_AFW5e_D + 1;
        HAP_AFW5e_pool := [];
        # Inlined linear fallback for this call.
        w2 := ShallowCopy(w);
        u := ShallowCopy(w);
        for x in v do
            r := Position(w2, [-x[1], x[2]]);
            if r = fail then
                Add(u, x);
            else
                u[r] := 0; w2[r] := 0;
            fi;
        od;
        return Filtered(u, i -> (not i = 0));
    fi;
    key := (g - 1) * stride + (c + D + 1);
    if IsBound(pool[key]) then
        Add(pool[key], i);
    else
        pool[key] := [i];
        Add(touched, key);
    fi;
od;

# Lookup. For each x = [c, g] in v, look up key for [-c, g].
# Entries that overflow current pool bounds can't possibly match anything
# in w (whose keys are bounded), so they fall through to Add(u, x).
for x in v do
    c := x[1];
    g := x[2];
    neg_c := -c;
    if AbsInt(neg_c) <= D and g <= HAP_AFW5e_G_max then
        key := (g - 1) * stride + (neg_c + D + 1);
        if IsBound(pool[key]) then
            entry := pool[key];
            u[entry[1]] := 0;
            if Length(entry) = 1 then
                Unbind(pool[key]);
            else
                Remove(entry, 1);
            fi;
            continue;
        fi;
    fi;
    Add(u, x);
od;

# Reset touched keys. O(|w|).
for i in [1..Length(touched)] do
    Unbind(pool[touched[i]]);
od;
HAP_AFW5e_touched := [];

return Filtered(u, i -> (not i = 0));
end);
#####################################################################

#####################################################################
InstallGlobalFunction(AppendFreeWord,
function(v,w)
local x,u,r, w2;

if Length(w)=0 then return false; fi;

for x in w do
   r:=Position(v,[-x[1],x[2]]);
   if r=fail then Add(v,x);
   else v[r]:=0;fi;
od;

v:=Filtered(v,x->not x=0);

return true;
end);
#####################################################################


#####################################################################
InstallGlobalFunction(AddFreeWordsModP,
function(v,w,p)
local x, SM,vw,i,j,ab;

if Length(v)=0 then return w; fi;
if Length(w)=0 then return v; fi;


	########################### if p=2 #############################
if p = 2 then

SM:=[];

for x in v do
if not IsBound(SM[x[2]]) then SM[x[2]]:=[]; fi;
ab:=AbsInt(x[1]);
if not IsBound(SM[x[2]][ab]) then
	SM[x[2]][ab]:=[ab,x[2]];
else
Unbind(SM[x[2]][ab]);
fi;
od;

for x in w do
if not IsBound(SM[x[2]]) then SM[x[2]]:=[]; fi;
ab:=AbsInt(x[1]);
if not IsBound(SM[x[2]][ab]) then
        SM[x[2]][ab]:=[ab,x[2]];
else
Unbind(SM[x[2]][ab]);
fi;
od;


vw:=[];
for x in SM do
for j in x do
Add(vw,j);
od;
od;


return vw;

fi;
	########################## fi p=2 ###########################

return AddFreeWords(v,w);
end);
#####################################################################

#####################################################################
InstallGlobalFunction(PrintZGword,
function(w,Elts)
local word, basis, coeffs, i, x, PrintGroupElt;

word:=AlgebraicReduction(w);
basis:=SSortedList(List(word, x->AbsoluteValue(x[1])));
coeffs:=[];

for i in basis do
coeffs[i]:=[];
od;

for x in word do
Append(coeffs[AbsoluteValue(x[1])],[SignInt(x[1])*x[2]]);
od;

	#############################################################
	PrintGroupElt:=function(i);
	if i>0 then Print("+ ", Elts[i], " ");
	else
	Print("- ", Elts[-i], " ");
	fi;
	end;
	#############################################################

for i in basis do
Print("( ");
	for x in coeffs[i] do
	PrintGroupElt(x);
	od;

if not i=Maximum(basis) then
Print(")E",i," +  ");
else
Print(")E",i,"\n");
fi;
od;
end);
#####################################################################

#####################################################################
InstallGlobalFunction(MultiplyWord,
function(n,w)
local v, u, i,x;
if n=1 then return w; fi;

v:=[];

u:=1*w;
if n<=0 then for x in u do x[1]:=-x[1]; od; fi;

for i in [1..AbsoluteValue(n)] do
Append(v,u);
od;

return 1*v;
end);
#####################################################################

#####################################################################
InstallGlobalFunction(WordModP,
function(w,p)
local u, v, y;

v:=Collected(w);
v:=List(v,x->[x[1],x[2] mod p]);
u:=[];
for y in v do
u:=AddFreeWords(u, MultiplyWord(y[2],[y[1]]));
od;

return u;
end);
#####################################################################

#####################################################################
InstallGlobalFunction(OppositeGroup,
function(w)
local u, v, y;

return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallGlobalFunction(QuotientGroup,
function(w,D)
local u, v, y;

return Objectify(HapQuotientElement,
                    rec(
                    element:=w*D) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( \*,
    "composition in opposite group",
    [ IsHapOppositeElement, IsHapOppositeElement],

function(x,y) local w;
w:=y!.element*x!.element;
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( \*,
    "composition in quotient group",
    [ IsHapQuotientElement, IsHapQuotientElement],

function(x,y) local w;
w:=x!.element[1]*y!.element;
return Objectify(HapQuotientElement,
                    rec(
                    element:=w) );
end);
#####################################################################


#####################################################################
InstallOtherMethod( \^,
    "inverse in opposite group",
    [ IsHapOppositeElement, IsInt],

function(x,n) local w;
w:=(x!.element)^n;
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( \^,
    "inverse in quotient group",
    [ IsHapQuotientElement, IsInt],

function(x,n) local w;
w:=(x!.element[1])^n;
w:=(w*x!.element[1]^-1)*x!.element;
return Objectify(HapQuotientElement,
                    rec(
                    element:=w) );
end);
#####################################################################




#####################################################################
InstallOtherMethod( \^,
    "inverse in opposite group",
    [ IsHapOppositeElement, IsHapOppositeElement],

function(x,y) local w;
w:=(x!.element)^y!.element;
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( \^,
    "inverse in quotient group",
    [ IsHapQuotientElement, IsHapQuotientElement],

function(x,y) local w,D;
w:=x!.element[1]^y!.element[1];
D:=x!.element[1]^-1*x!.element;
w:=w*D;
return Objectify(HapQuotientElement,
                    rec(
                    element:=w) );
end);
#####################################################################


#####################################################################
InstallOtherMethod( One,
    "identity in opposite group",
    [ IsHapOppositeElement],

function(x) local w;
w:=One(x!.element);
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( One,
    "identity in quotient group",
    [ IsHapQuotientElement],

function(x) local w;
w:=x!.element[1]^-1;
w:=w*x!.element;
return Objectify(HapQuotientElement,
                    rec(
                    element:=w) );
end);
#####################################################################


#####################################################################
InstallOtherMethod( InverseMutable,
    "inverse in opposite group",
    [ IsHapOppositeElement],

function(x) local w;
w:=InverseMutable(x!.element);
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################

#####################################################################
InstallOtherMethod( InverseMutable,
    "inverse in quotient group",
    [ IsHapQuotientElement],

function(x) local w;
w:=List(x!.element,InverseMutable);
return Objectify(HapOppositeElement,
                    rec(
                    element:=w) );
end);
#####################################################################


#####################################################################
InstallOtherMethod( \=,
    "equality in opposite group",
    [ IsHapOppositeElement, IsHapOppositeElement],

function(x,y) ;
return  x!.element = y!.element;
end);
#####################################################################

#####################################################################
InstallOtherMethod( \=,
    "equality in quotient group",
    [ IsHapQuotientElement, IsHapQuotientElement],

function(x,y) ;
return  SSortedList(x!.element) = SSortedList(y!.element);
end);
#####################################################################


#####################################################################
InstallOtherMethod( \<,
    "equality in opposite group",
    [ IsHapOppositeElement, IsHapOppositeElement],

function(x,y) ;
return  x!.element < y!.element;
end);
#####################################################################

#####################################################################
InstallOtherMethod( \<,
    "equality in opposite group",
    [ IsHapQuotientElement, IsHapQuotientElement],

function(x,y) ;
return  SSortedList(x!.element) < SSortedList(y!.element);
end);
#####################################################################



###############################################################
###############################################################
InstallGlobalFunction(ResolutionBoundaryOfWord,
function(R,n,W)
local x, DW, Boundary, Dimension,Elts,pos, ans;

Dimension:=R!.dimension;
Boundary:=R!.boundary;
Elts:=R!.elts;
DW:=[];

for x in W do
ans:=Boundary(n,x[1]);
ans:=List(ans, a->[a[1],Elts[a[2]]]);
ans:=List(ans, a->[a[1],Elts[x[2]]*a[2]]);
Append(DW,ans);
od;

DW:= AlgebraicReduction(DW);
for x in DW do
if not x[2] in Elts then Add(Elts,x[2]);fi;
od;
DW:=List(DW,x->[x[1],Position(Elts,x[2])]);
return DW;

end);
###############################################################
###############################################################


