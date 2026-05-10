# test_centraliser_cache.g — same centraliser type uses the same resolution.
#
# E_+(2) = SmallGroup(32, 49) has 17 conjugacy classes whose centralisers
# realise three iso-types:
#   [32, 49]  for classes 1, 6      (the whole group, central elements)
#   [16, 11]  for classes 2, 3, 4, 5, 8, 11, 12, 13, 14
#   [16, 13]  for classes 7, 9, 10, 15, 16, 17
#
# We use:
#   classes 2 & 3 — distinct classes with isomorphic centralisers ([16, 11]).
#                  Cache MUST return the same record (IsIdenticalObj = true).
#   classes 2 & 7 — distinct classes with non-isomorphic centralisers
#                  ([16, 11] vs [16, 13]). Cache MUST return DIFFERENT records.
#   class 1       — third iso-type ([32, 49]); third independent cache entry.

Read("../centraliser_cache.g");

G := SmallGroup(32, 49);;
classes := ConjugacyClasses(G);;

rep_a := Representative(classes[2]);;   # IdGroup(C) = [16, 11]
rep_b := Representative(classes[3]);;   # IdGroup(C) = [16, 11], same iso-type as rep_a
rep_c := Representative(classes[7]);;   # IdGroup(C) = [16, 13], different iso-type
rep_d := Representative(classes[1]);;   # IdGroup(C) = [32, 49] (identity, full group)

# Sanity: distinct conjugacy classes (so we are really exercising the cache,
# not just calling the function with the same input twice).
Assert(0, not IsConjugate(G, rep_a, rep_b),
       "classes[2] and classes[3] must be non-conjugate to test the cache");
Assert(0, not IsConjugate(G, rep_a, rep_c),
       "classes[2] and classes[7] must be non-conjugate");

# Sanity: pre-condition on iso-types.
Assert(0, IdGroup(Centralizer(G, rep_a)) = [16, 11],
       "rep_a centraliser must be [16, 11]");
Assert(0, IdGroup(Centralizer(G, rep_b)) = [16, 11],
       "rep_b centraliser must be [16, 11]");
Assert(0, IdGroup(Centralizer(G, rep_c)) = [16, 13],
       "rep_c centraliser must be [16, 13]");
Assert(0, IdGroup(Centralizer(G, rep_d)) = [32, 49],
       "rep_d centraliser must be [32, 49]");

data_a := GetCentraliserData(G, rep_a);;
data_b := GetCentraliserData(G, rep_b);;
data_c := GetCentraliserData(G, rep_c);;
data_d := GetCentraliserData(G, rep_d);;

# Same iso-type -> identical cache record.
Assert(0, IsIdenticalObj(data_a, data_b),
       "two reps with isomorphic centralisers must share the cache record");

# Different iso-type -> different cache records.
Assert(0, not IsIdenticalObj(data_a, data_c),
       "reps with non-isomorphic centralisers must NOT share a record");
Assert(0, not IsIdenticalObj(data_a, data_d),
       "reps with non-isomorphic centralisers must NOT share a record");
Assert(0, not IsIdenticalObj(data_c, data_d),
       "reps with non-isomorphic centralisers must NOT share a record");

# Repeated call on rep_a returns the same cache record (idempotency).
Assert(0, IsIdenticalObj(data_a, GetCentraliserData(G, rep_a)),
       "second call on rep_a must hit the cache");

# Record shape: data.C is bound and matches the centraliser of the rep,
# data.R is a HAP resolution (object, not fail), data.bockstein_image is a list.
Assert(0, IsBound(data_a.C), "data.C must be bound");
Assert(0, IdGroup(data_a.C) = [16, 11], "data_a.C must have IdGroup [16, 11]");
Assert(0, IdGroup(data_c.C) = [16, 13], "data_c.C must have IdGroup [16, 13]");
Assert(0, IsBound(data_a.R), "data.R must be bound");
Assert(0, data_a.R <> fail, "data.R must not be fail");
Assert(0, IsBound(data_a.bockstein_image), "data.bockstein_image must be bound");
Assert(0, IsList(data_a.bockstein_image),
       "data.bockstein_image must be a list (BocksteinH1ToH2 output)");
Assert(0, IsBound(data_a.h2_basis), "data.h2_basis must be bound");

# Cache contains exactly three entries (one per iso-type seen).
Assert(0, Length(RecNames(CentraliserCache)) = 3,
       Concatenation("CentraliserCache must have 3 entries; got ",
                     String(Length(RecNames(CentraliserCache)))));

Print("test_centraliser_cache: PASS\n");
QUIT;
