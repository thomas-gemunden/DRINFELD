Read("em_construction.g");
Read("bw_lattice.g");

for m in [1, 2, 3] do
    VerifyEm(m);
od;

VerifyBW(1);
VerifyBW(2);
VerifyBW(3);
VerifyBW(4);

Print("\n=== Half-Gram H for m=3 (E_8) ===\n");
H3 := HalfGram(3);;
G3 := BWGram(3);;
Print("H + H^T = G: ", H3 + TransposedMat(H3) = G3, "\n");
Print("Discriminant 1 (E_8): ", DeterminantMat(G3) = 1, "\n");

QUIT;
