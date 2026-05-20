# test_em_eplus_translate.g
#
# Issue #256: regression tests for EmEPlusTranslate and
# TranslateSpectralDataToEPlus.
#
# Test cases:
#   T1. Smoke: EmEPlusTranslate, TranslateSpectralDataToEPlus,
#       TranslateElementEUtoEP, TranslateElementEPtoEU all bound.
#   T2. m = 2 isomorphism: bijective, commutator preserved.
#   T3. m = 3 isomorphism: bijective, commutator preserved.
#   T4. m = 5 isomorphism: hom built; generators mapped; commutator
#       on first pair preserved.
#   T5. m = 1 isomorphism: bijective via IsomorphismGroups fallback.
#   T6. Element round-trip: psi_inv . psi = id on EU generators
#       (m = 2, 3, 5).
#   T7. Class-image consistency: psi maps EU classes onto EP classes
#       bijectively (m = 2, 3) — i.e. the class-index translation
#       table built by TranslateSpectralDataToEPlus is bijective.
#   T8. Cross-validation via subgroup compatibility: at m = 3, the
#       image of EmUnimodGroup(3) under psi equals EPlusGroup(3) as a
#       set (Order(Image(psi)) = Order(EP)).

# Derive _TEST_DIR / _SCRIPT_DIR from the test file's own absolute path
# so the test runs unchanged across worktrees (#275 fix: was hardcoded
# to a stale predecessor worktree path).
_SCRIPT_SELF := INPUT_FILENAME();;
if _SCRIPT_SELF = fail or _SCRIPT_SELF = "stream" then
    Error("test_em_eplus_translate.g: INPUT_FILENAME() unavailable; ",
          "Read by absolute path.");
fi;
_TEST_DIR := _SCRIPT_SELF{
    [1..Length(_SCRIPT_SELF)
       - Length("/test_em_eplus_translate.g")]};;
_SCRIPT_DIR := _TEST_DIR{
    [1..Length(_TEST_DIR) - Length("/tests")]};;
ChangeDirectoryCurrent(_SCRIPT_DIR);

# Bookkeeping.
T_PASSES := 0;;
T_FAILURES := [];;

TAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        T_PASSES := T_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(T_FAILURES, label);
    fi;
end;;

TAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        T_PASSES := T_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(T_FAILURES, label);
    fi;
end;;

# Load deps in the right order.
Read(Concatenation(_SCRIPT_DIR, "/em_construction.g"));
Read(Concatenation(_SCRIPT_DIR, "/bw_lattice.g"));
Read(Concatenation(_SCRIPT_DIR, "/twisted_group_algebra.g"));
Read(Concatenation(_SCRIPT_DIR, "/krr_spectral_characters.g"));
Read(Concatenation(_SCRIPT_DIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_SCRIPT_DIR, "/em_eplus_translate.g"));

Print("\n=================================================================\n");
Print("T1: smoke - binding check\n");
Print("=================================================================\n");

TAssertTrue("EmEPlusTranslate bound", IsBound(EmEPlusTranslate));
TAssertTrue("TranslateSpectralDataToEPlus bound",
            IsBound(TranslateSpectralDataToEPlus));
TAssertTrue("TranslateElementEUtoEP bound",
            IsBound(TranslateElementEUtoEP));
TAssertTrue("TranslateElementEPtoEU bound",
            IsBound(TranslateElementEPtoEU));

Print("\n=================================================================\n");
Print("T2: m = 2 isomorphism\n");
Print("=================================================================\n");

T2_REC := EmEPlusTranslate(2);;
TAssertTrue("T2: rec.psi <> fail", T2_REC.psi <> fail);
TAssertEqual("T2: Source(psi) = EU", Source(T2_REC.psi), T2_REC.EU);
TAssertEqual("T2: Range(psi) = EP", Range(T2_REC.psi), T2_REC.EP);
TAssertTrue("T2: IsBijective(psi)", IsBijective(T2_REC.psi));
# Commutator preservation: [σ_{1,1}, σ_{1,2}] = z.
T2_GENS_EU := GeneratorsOfGroup(T2_REC.EU);;
T2_C := Comm(T2_GENS_EU[2], T2_GENS_EU[3]);;
T2_IMG_C := Image(T2_REC.psi, T2_C);;
T2_IMG_Z := Image(T2_REC.psi, T2_GENS_EU[1]);;
TAssertEqual("T2: psi([σ_{1,1}, σ_{1,2}]) = psi(z)", T2_IMG_C, T2_IMG_Z);

Print("\n=================================================================\n");
Print("T3: m = 3 isomorphism\n");
Print("=================================================================\n");

T3_REC := EmEPlusTranslate(3);;
TAssertTrue("T3: rec.psi <> fail", T3_REC.psi <> fail);
TAssertTrue("T3: IsBijective(psi)", IsBijective(T3_REC.psi));
T3_GENS_EU := GeneratorsOfGroup(T3_REC.EU);;
T3_C := Comm(T3_GENS_EU[2], T3_GENS_EU[3]);;
TAssertEqual("T3: psi([σ_{1,1}, σ_{1,2}]) = psi(z)",
             Image(T3_REC.psi, T3_C),
             Image(T3_REC.psi, T3_GENS_EU[1]));
# Off-pair commutator should be identity.
T3_C_OFF := Comm(T3_GENS_EU[2], T3_GENS_EU[4]);;  # σ_{1,1} vs σ_{2,1}: commute
TAssertTrue("T3: psi([σ_{1,1}, σ_{2,1}]) = One(EP) (off-pair)",
            IsOne(Image(T3_REC.psi, T3_C_OFF)));

Print("\n=================================================================\n");
Print("T4: m = 5 isomorphism\n");
Print("=================================================================\n");

T4_REC := EmEPlusTranslate(5);;
TAssertTrue("T4: rec.psi <> fail", T4_REC.psi <> fail);
# IsBijective at m=5 is expensive (~30s) but tractable; the matrix
# group EU has order 2048. We use Order(Image(psi)) = Order(EP) as a
# cheaper proxy.
T4_IMG_ORD := Order(Image(T4_REC.psi));;
TAssertEqual("T4: Order(Image(psi)) = Order(EP) (= 2048)",
             T4_IMG_ORD, Order(T4_REC.EP));
T4_GENS_EU := GeneratorsOfGroup(T4_REC.EU);;
T4_C := Comm(T4_GENS_EU[2], T4_GENS_EU[3]);;
TAssertEqual("T4: psi([σ_{1,1}, σ_{1,2}]) = psi(z) at m=5",
             Image(T4_REC.psi, T4_C),
             Image(T4_REC.psi, T4_GENS_EU[1]));

Print("\n=================================================================\n");
Print("T5: m = 1 isomorphism (fallback IsomorphismGroups)\n");
Print("=================================================================\n");

T5_REC := EmEPlusTranslate(1);;
TAssertTrue("T5: rec.psi <> fail", T5_REC.psi <> fail);
TAssertTrue("T5: IsBijective(psi)", IsBijective(T5_REC.psi));
TAssertEqual("T5: |Source| = |Range| = 8",
             Order(Source(T5_REC.psi)), 8);

Print("\n=================================================================\n");
Print("T6: round-trip psi_inv . psi = id on generators\n");
Print("=================================================================\n");

for T6_M in [2, 3, 5] do
    T6_REC := EmEPlusTranslate(T6_M);;
    T6_GENS := GeneratorsOfGroup(T6_REC.EU);;
    T6_OK := true;;
    for T6_G in T6_GENS do
        if Image(T6_REC.psi_inv, Image(T6_REC.psi, T6_G)) <> T6_G then
            T6_OK := false;
            break;
        fi;
    od;
    TAssertTrue(Concatenation("T6: round-trip on EU gens at m=",
                              String(T6_M)),
                T6_OK);
od;

Print("\n=================================================================\n");
Print("T7: class-image consistency (m = 2, 3)\n");
Print("=================================================================\n");

for T7_M in [2, 3] do
    T7_REC := EmEPlusTranslate(T7_M);;
    T7_EU_CLASSES := ConjugacyClasses(T7_REC.EU);;
    T7_EP_CLASSES := ConjugacyClasses(T7_REC.EP);;
    TAssertEqual(Concatenation(
            "T7: same # classes at m=", String(T7_M)),
        Length(T7_EU_CLASSES), Length(T7_EP_CLASSES));
    # For each EU class, the image of its rep should land in exactly
    # one EP class. Build the EU-class -> EP-class map and check
    # injectivity (-> bijectivity by pigeon).
    T7_EU_TO_EP := List(T7_EU_CLASSES, c -> First([1..Length(T7_EP_CLASSES)],
        k -> Image(T7_REC.psi, Representative(c))
             in T7_EP_CLASSES[k]));;
    TAssertTrue(Concatenation(
            "T7: EU->EP class map is total at m=", String(T7_M)),
        not (fail in T7_EU_TO_EP));
    TAssertEqual(Concatenation(
            "T7: EU->EP class map is bijective at m=", String(T7_M)),
        Length(Set(T7_EU_TO_EP)), Length(T7_EP_CLASSES));
od;

Print("\n=================================================================\n");
Print("T8: cross-validation - Image(psi) = EP as sets\n");
Print("=================================================================\n");

for T8_M in [2, 3] do
    T8_REC := EmEPlusTranslate(T8_M);;
    TAssertEqual(Concatenation(
            "T8: Order(Image(psi)) = Order(EP) at m=", String(T8_M)),
        Order(Image(T8_REC.psi)), Order(T8_REC.EP));
od;

Print("\n=================================================================\n");
Print("T9: psi preserves element orders and pairwise multiplications\n");
Print("=================================================================\n");

# T9a: orders preserved on all generators (m = 2, 3).
for T9_M in [2, 3] do
    T9_REC := EmEPlusTranslate(T9_M);;
    T9_GENS_EU := GeneratorsOfGroup(T9_REC.EU);;
    T9_ORDERS_OK := ForAll(T9_GENS_EU,
        g -> Order(g) = Order(Image(T9_REC.psi, g)));;
    TAssertTrue(Concatenation(
            "T9a: psi preserves generator orders at m=", String(T9_M)),
        T9_ORDERS_OK);
od;

# T9b: psi is a homomorphism: psi(a * b) = psi(a) * psi(b) for all
#      pairs of generators (m = 2, 3).
for T9_M in [2, 3] do
    T9_REC := EmEPlusTranslate(T9_M);;
    T9_GENS_EU := GeneratorsOfGroup(T9_REC.EU);;
    T9_HOM_OK := true;;
    for T9_I in [1..Length(T9_GENS_EU)] do
        for T9_J in [1..Length(T9_GENS_EU)] do
            T9_A := T9_GENS_EU[T9_I];;
            T9_B := T9_GENS_EU[T9_J];;
            T9_PROD := T9_A * T9_B;;
            T9_IMG_PROD := Image(T9_REC.psi, T9_PROD);;
            T9_PROD_IMG := Image(T9_REC.psi, T9_A) * Image(T9_REC.psi, T9_B);;
            if T9_IMG_PROD <> T9_PROD_IMG then
                T9_HOM_OK := false;
                break;
            fi;
        od;
        if not T9_HOM_OK then break; fi;
    od;
    TAssertTrue(Concatenation(
            "T9b: psi(a*b) = psi(a)*psi(b) on all generator pairs at m=",
            String(T9_M)),
        T9_HOM_OK);
od;

# T9c: orders preserved on a sample of elements (m = 5).
T9_REC5 := EmEPlusTranslate(5);;
T9_GENS_EU5 := GeneratorsOfGroup(T9_REC5.EU);;
T9_ORDERS_OK5 := ForAll(T9_GENS_EU5,
    g -> Order(g) = Order(Image(T9_REC5.psi, g)));;
TAssertTrue("T9c: psi preserves generator orders at m=5", T9_ORDERS_OK5);
# Also sample some products at m=5.
T9_PROD5_OK := true;;
for T9_I in [1..Length(T9_GENS_EU5)] do
    for T9_J in [T9_I..Length(T9_GENS_EU5)] do
        T9_A5 := T9_GENS_EU5[T9_I];;
        T9_B5 := T9_GENS_EU5[T9_J];;
        T9_PROD5 := T9_A5 * T9_B5;;
        if Image(T9_REC5.psi, T9_PROD5) <>
           Image(T9_REC5.psi, T9_A5) * Image(T9_REC5.psi, T9_B5) then
            T9_PROD5_OK := false;
            break;
        fi;
    od;
    if not T9_PROD5_OK then break; fi;
od;
TAssertTrue("T9c: psi(a*b) = psi(a)*psi(b) on generator pairs at m=5",
            T9_PROD5_OK);

Print("\n=================================================================\n");
Print("Summary: ", T_PASSES, " passes, ", Length(T_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(T_FAILURES) = 0 then
    Print("\nPASS test_em_eplus_translate\n");
else
    Print("\nFAIL test_em_eplus_translate:\n");
    for T_F in T_FAILURES do
        Print("  - ", T_F, "\n");
    od;
fi;

QUIT;
