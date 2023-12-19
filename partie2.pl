
% Acquisition des propositions de type 1

acquisition_prop_type1(Abi, Abi1, Tbox) :- 
    write('Entrez I :'),nl, 
    read(I), writef('I : %w', [I]), nl, nl,
    write('Entrez C :'),nl, 
    read(CG), writef('C : %w', [C]), nl, nl,
    (instanciationC(I, CG) -> % if 
        writef('%w : %w', [I, CG])
        ; ( % else
        write('\[ERREUR] : I n\'est pas une instance déclarée ou C n\'est pas un concept'), nl,
        write('A nouveau'), nl, fail
    )),
    transforme([(I,not(CG))], [(I, CG_dev_nnf)]), % Développement + nnf
    concat(Abi,[(I, CG_dev_nnf)], Abi1), % Ajout de l input  dans la ABox
    %write("Abi1"), write(Abi1),
    nl. 




% Acquisition des propositions de type 2

acquisition_prop_type2(Abi, Abi1, Tbox) :- 
   read(C1), nl, writef('C1 : %w', [C1]), nl, nl,
    write('Entrez C2 :'), nl, 
    read(C2),nl, writef('C2 : %w', [C2]), nl, nl,
    (concept(and(C1, C2)) -> % if 
        writef("%w ⊓ %w ⊑ ⊥", [C1, C2])
        ; ( % else
        write('[ERREUR] : C1 ou C2 n\'est pas un concept déclaré'), nl,
        write('A nouveau'), nl, fail
    )),
    genere(Random_CName),
    transforme([(Random_CName, and(C1, C2))], [(Random_CName, and(C1_dev_nnf, C2_dev_nnf))]),
    concat(Abi, [(Random_CName, and(C1_dev_nnf, C2_dev_nnf))], Abi1), % Ajout de l input dans la ABox
    %write("Abi1"), write(Abi1),
    nl.