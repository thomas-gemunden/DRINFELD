# install_addfreewords_patch.g — runtime hot-patch of HAP's AddFreeWords.
#
# A-7 perf-5e (#284), fallback delivery mode.
#
# The original plan (issue #284 / Route A) was to edit the HAP source file
# `/opt/homebrew/.../pkg/hap/lib/FreeGmodules/wordOperations.gi` directly
# and recompile via `compile.sh`. That requires write permission to the
# Homebrew-owned HAP directory, which is not available inside this
# subagent's sandbox. This file is a runtime hot-patch alternative.
#
# Read this file AFTER `LoadPackage("hap");` (i.e. after HAP installs its
# original AddFreeWords). It rebinds AddFreeWords to the perf-5e
# positional-pool variant. Subsequent HAP code that calls AddFreeWords
# (including inside Syzygy/Homotopy) goes through the patched version.
#
# Tradeoffs vs the .gi-patch+compile route:
#   - INTERPRETED GAP (matches the .gi-without-compile path).
#     For an additional .so-compiled speedup, the user must apply the
#     patch to /opt/homebrew/.../wordOperations.gi and run compile.sh.
#   - No change to /opt/homebrew, so `brew upgrade gap` does NOT wipe
#     this; just re-Read the install file in the new GAP session.
#
# Usage:
#
#   LoadPackage("hap");
#   Read("<DRINFELD>/extraspecial_orbifolds/hap_patches/install_addfreewords_patch.g");
#
# Verification: see tests/test_perf5e_hap_addfreewords.g.

# Single module-level state record. Names are HAP_AFW5e_* to avoid
# clobbering anything else in the GAP session.
if not IsBoundGlobal("HAP_AFW5e_state") then
    BindGlobal("HAP_AFW5e_state", rec(pool := [],
                                      touched := [],
                                      D := 64,
                                      G_max := 64,
                                      stride := 2 * 64 + 1,
                                      MIN_SMALL := 24));
fi;

# Internal helper: original HAP linear-scan AddFreeWords. We use this
# (a) as the fall-through for small inputs, and (b) as the safety net
# when (c, g) values overflow the current pool bounds.
HAP_AFW5e_LinearScan := function(arg1, arg2)
    local x, u, v, w, r, w2;
    if Length(arg2) < Length(arg1) then
        v := arg1; w := arg2;
    else
        w := arg1; v := arg2;
    fi;
    if Length(w) = 0 then return v; fi;
    if Length(v) = 0 then return w; fi;
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
    u := Filtered(u, i -> (not i = 0));
    return u;
end;;

# Patched AddFreeWords. Bit-identical output for any input; algorithm
# is the same positional-pool scheme used in perf-5c's _AddFreeWordsFast
# (see extraspecial_orbifolds/scripts/solver/snf_wrapper.g for the
# math + perf rationale).
#
# Use a function with a fixed arg list `arg` to match HAP's variadic
# declaration. HAP's AddFreeWords is `function(arg) ... end`, where
# `arg` is the list of actual arguments.
#
# Small-input path is INLINED (not delegated to HAP_AFW5e_LinearScan).
# HAP's Syzygy() calls AddFreeWords many times on length-2 sub-syzygy
# combines where both sides are tiny. The overhead of an extra GAP-level
# function call on each of those was measurable at m=3 (caches wall
# went UP from perf-5c's 19s to 23s with the indirection). Inlining
# reverts to roughly perf-5c performance on small calls while still
# getting the pool benefit on large calls.
HAP_AFW5e_Fast := function(arg)
    local arg1, arg2, v, w, u, w_len, v_len, x, c, g, key, entry, neg_c,
          i, r, w2, st, pool, touched, stride, D, max_g, max_c, ic;

    if Length(arg) < 2 then
        Error("AddFreeWords expects 2 arguments");
    fi;
    arg1 := arg[1];
    arg2 := arg[2];

    if Length(arg2) < Length(arg1) then
        v := arg1; w := arg2;
    else
        w := arg1; v := arg2;
    fi;

    w_len := Length(w);
    v_len := Length(v);
    if w_len = 0 then return v; fi;
    if v_len = 0 then return w; fi;

    st := HAP_AFW5e_state;
    # Inlined linear-scan path for small inputs. Avoids the extra function
    # call we used to do via HAP_AFW5e_LinearScan, which on m=3 minus_one
    # added more overhead than the dict path saved.
    if w_len < st.MIN_SMALL then
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

    pool := st.pool;
    touched := st.touched;
    stride := st.stride;
    D := st.D;

    u := ShallowCopy(w);

    max_c := 0; max_g := 0;
    for i in [1..w_len] do
        c := w[i][1];
        g := w[i][2];
        ic := AbsInt(c);
        if ic > max_c then max_c := ic; fi;
        if g > max_g then max_g := g; fi;
        if max_c > D or max_g > st.G_max then
            # Reset what we set so far.
            for key in touched do Unbind(pool[key]); od;
            st.touched := [];
            # Grow capacity; stride changes -> pool is invalidated.
            if max_c > st.D then st.D := max_c; fi;
            if max_g > st.G_max then st.G_max := max_g; fi;
            st.stride := 2 * st.D + 1;
            st.pool := [];
            return HAP_AFW5e_LinearScan(arg1, arg2);
        fi;
        key := (g - 1) * stride + (c + D + 1);
        if IsBound(pool[key]) then
            Add(pool[key], i);
        else
            pool[key] := [i];
            Add(touched, key);
        fi;
    od;

    for x in v do
        c := x[1];
        g := x[2];
        neg_c := -c;
        if AbsInt(neg_c) <= D and g <= st.G_max then
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

    for i in [1..Length(touched)] do
        Unbind(pool[touched[i]]);
    od;
    st.touched := [];

    return Filtered(u, i -> (not i = 0));
end;;

# Capture a reference to HAP's original implementation (for self-check
# comparisons later if needed). HAP's AddFreeWords lives at the GLOBAL
# `AddFreeWords` after LoadPackage("hap") has run; the global is bound
# to a callable.
if IsBoundGlobal("HAP_AFW5e_OriginalAddFreeWords") then
    # Already captured by a previous Read; don't overwrite.
else
    if IsBoundGlobal("AddFreeWords") then
        BindGlobal("HAP_AFW5e_OriginalAddFreeWords", ValueGlobal("AddFreeWords"));
    else
        Error("install_addfreewords_patch: AddFreeWords is not bound. ",
              "Did you LoadPackage(\"hap\") before Read'ing this file?");
    fi;
fi;

# Install the patch. AddFreeWords was declared via DeclareGlobalFunction
# in hap.gd, then installed in wordOperations.gi by InstallGlobalFunction.
# We need to replace the function attached to this global. The simplest
# robust approach: unbind the global, then re-declare + re-install.
# This avoids any read-only protection that HAP may have set.
MakeReadWriteGlobal("AddFreeWords");
UnbindGlobal("AddFreeWords");
DeclareGlobalFunction("AddFreeWords");
InstallGlobalFunction(AddFreeWords, HAP_AFW5e_Fast);

# Post-install self-check: verify the patch is wired up and a basic
# cancellation works.
if AddFreeWords([[1, 1], [-1, 2]], [[1, 2], [-1, 1]]) <> [] then
    Error("install_addfreewords_patch: post-install self-check failed");
fi;
# Larger input check: 30-entry vs 3-entry should exercise the pool path.
if Length(AddFreeWords(List([1..30], i -> [i, 1]), [[-15, 1], [-25, 1], [-7, 1]])) <> 27 then
    Error("install_addfreewords_patch: large-input self-check failed");
fi;

Print("[perf-5e] HAP AddFreeWords patched (positional-pool, threshold ",
      HAP_AFW5e_state.MIN_SMALL, ")\n");
