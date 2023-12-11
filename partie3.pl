%/* Tri Abox %/*

tri_Abox([],[],[],[],[],[]).

tri_Abox([(I,some(R,C)) | Abi], [(I,some(R,C)) | Lie], Lpt, Li, Lu, Ls):- 
    tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).

tri_Abox([(I,all(R,C)) | Abi], Lie, [(I,all(R,C)) | Lpt], Li, Lu, Ls):- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,and(C1,C2)) | Abi], Lie, Lpt, [(I,and(C1,C2)) | Li], Lu, Ls):- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,or(C1,C2)) | Abi], Lie, Lpt, Li, [(I,or(C1,C2)) | Lu], Ls):- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls).

tri_Abox([(I,not(C)) | Abi], Lie, Lpt, Li, Lu, [(I,not(C)) | Ls]):- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls), cnamea(C).

tri_Abox([(I,C) | Abi], Lie, Lpt, Li, Lu, [(I,C) | Ls]):- 
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls), cnamea(C).





%/* Evolution des listes */%

/*Exist*/
evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, [(I,some(R,C)) | Lie], Lpt, Li, Lu, Ls):- 
    \+ member((I,some(R,C)), Lie).
evolue((I,some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,some(R,C)), Lie).

/*For all*/
evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I,some(R,C)) | Lpt], Li, Lu, Ls):- 
    \+ member((I,all(R,C)), Lpt).
evolue((I,all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,some(R,C)), Lpt).

/*And*/
evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I,and(C1,C2)) | Li], Lu, Ls):- 
    \+ member((I,and(C1,C2)), Li).
evolue((I,and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,and(C1,C2)), Li).

/*Or*/
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I,and(C1,C2)) | Lu], Ls):- 
    \+ member((I,or(C1,C2)), Lu).
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,or(C1,C2)), Lu).

/*Assertions restantes (avec concepts atomiques)*/
evolue((I,not(C)) Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I,not(C)) | Ls]):- 
    \+ member((I,not(C)), Ls), 
    cnamea(C).
evolue((I,not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,not(C)), Ls), 
    cnamea(C).

evolue((I,C) Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I,C) | Ls]):- 
    \+ member((I,C), Ls), 
    cnamea(C).
evolue((I,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,C), Ls), 
    cnamea(C).






%/* Règles */%


/*Règle ∃*/
complete_some([(A,some(R,C)) | Lie], Lpt, Li, Lu, Ls, Abr):- 
    % crée un nouvel objet b
    genere(B), 

    % ajoute assertion b : C
    evolue((B, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),        

    % ajoute assertion <a, b> : R et continue la résolution
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, [(A, B, R) | Abr]).               


/*Règle ⊓*/
transformation_and(Lie, Lpt, [(A,and(C,D)) | Li], Lu, Ls, Abr):-
    % ajoute assertion a : C
    evolue((A, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),

    % ajoute assertion a : D
    evolue((A, D), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2), 

    % continue la résolution
    resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr). 


/*Règle ∀*/
deduction_all(Lie,Lpt,Li,Lu,Ls,Abr).

transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).



%/* Affichage */%

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2).





%/* Démonstration */%

resolution(Lie,Lpt,Li,Lu,Ls,Abr):-complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
                                transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
                                deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
                                transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).


troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl,write('Youpiiiiii, on a demontre la
                            proposition initiale !!!').