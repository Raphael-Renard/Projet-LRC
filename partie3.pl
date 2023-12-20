:- encoding(utf8).


concept(C) :- cnamea(C). % à enlever après ajout de partie 1
concept(CG) :- cnamena(CG). % à enlever après ajout de partie 1



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
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I,or(C1,C2)) | Lu], Ls):- 
    \+ member((I,or(C1,C2)), Lu).
evolue((I,or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,or(C1,C2)), Lu).

/*Assertions restantes (avec concepts atomiques)*/
evolue((I,not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I,not(C)) | Ls]):- 
    \+ member((I,not(C)), Ls), 
    cnamea(C).
evolue((I,not(C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,not(C)), Ls), 
    cnamea(C).

evolue((I,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [(I,C) | Ls]):- 
    \+ member((I,C), Ls), 
    cnamea(C).
evolue((I,C), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls):- 
    member((I,C), Ls), 
    cnamea(C).

/*Mise à jour récursive*/
evolue_plusieurs([], Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls).
evolue_plusieurs([A|L], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) :-
    evolue(A, Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
    evolue_plusieurs(L, Lie2, Lpt2, Li2, Lu2, Ls2, Lie1, Lpt1, Li1, Lu1, Ls1).




%/* Règles */%


/*Règle ∃*/
complete_some([(A,some(R,C)) | Lie], Lpt, Li, Lu, Ls, Abr):- 
    % crée un nouvel objet b
    genere(B), 

    % ajoute assertion b : C
    evolue((B, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
    
    % affichage
    write("On applique la règle  \u2203 sur "), affichage([(A,some(R,C))]),nl,
    affiche_evolution_Abox(Ls, [(A,some(R,C)) | Lie], Lpt, Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, [(A, B, R) | Abr]),   

    % ajoute assertion <a, b> : R et continue la résolution
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, [(A, B, R) | Abr]).               


/*Règle ⊓*/
transformation_and(Lie, Lpt, [(A,and(C,D)) | Li], Lu, Ls, Abr):-
    % ajoute assertion a : c et a : d
    evolue_plusieurs([(A, C),(A, D)], Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),

    % affichage
    write("On applique la règle \u2293 sur "), affichage([(A,and(C,D))]),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, [(A,and(C,D)) | Li], Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),

    % continue la résolution
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr). 


/*Règle ∀*/
deduction_all(Lie,[(A,all(R,C)) | Lpt], Li, Lu, Ls, Abr):- 
    nl,

    % crée liste L_BC pour avec tous les B apparaissant dans une assertion du type (A,B,R)
    setof((B, C),  member((A, B, R), Abr), L_BC),

    % crée liste L_ABR de toutes les assertions du type (A,B,R)
    setof((A, B, R),  member((A, B, R), Abr), L_ABR),

    % affichage des instances sur lequelles on applique la règle
    affichage_forall(L_ABR),


    % ajoute assertions b : c
    evolue_plusieurs(L_BC, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),

    % affichage
    affiche_evolution_Abox(Ls, Lie, [(A,all(R,C)) | Lpt], Li, Lu, Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),

    % continue la résolution
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr).



deduction_all(Lie,[(A,all(R,C)) | Lpt], Li, Lu, Ls, Abr):- 
    \+ member((A,B,C),Abr), 

    % continue la résolution
    resolution(Lie, Lpt, Li, Lu, Ls, Abr).


/* Règle ⊔*/
transformation_or(Lie, Lpt, Li, [(A,or(C,D)) | Lu], Ls, Abr):-
    % ajoute assertion a : C à la première branche
    evolue((A, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),

    % affichage
    nl,
    write("On applique la règle  \u2294 sur "), affichage([(A,or(C,D))]), write("(première branche)"),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(A,or(C,D)) | Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),

    % continue la résolution de la première branche
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr).


transformation_or(Lie, Lpt, Li, [(A,or(C,D)) | Lu], Ls, Abr):-
    % ajoute assertion a : D à la deuxième branche
    evolue((A, D), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),

    % affichage
    nl,
    write("On applique la règle  \u2294 sur "), affichage([(A,or(C,D))]), write("(deuxième branche)"),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(A,or(C,D)) | Lu], Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),

    % continue la résolution de la deuxième branche
    resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr).






%/* Affichage */% 

affichage_forall([]).
affichage_forall([(A,B,R)|L_instR]):- 
    write("On applique la règle \u2200 sur "), affichageR([(A,B,R)]), nl,
    affichage_forall(L_instR).


affichage([]).

affichage(C) :- concept(C), write(C).
affichage(I) :- iname(I), write(I).
affichage(not(C)) :- write(" \u00AC "), affichage(C). % ¬
affichage(or(C1, C2)) :- affichage(C1), write(' \u2294 '), affichage(C2). % ⊔
affichage(and(C1, C2)) :- affichage(C1), write(' \u2293 '), affichage(C2). % ⊓
affichage(some(R, C)) :- write(' \u2203 '), write(R), write('.'), affichage(C). % ∃
affichage(all(R, C)) :- write(' \u2200 '), write(R), write('.'), affichage(C). % ∀

affichage([(I, C) | L]):-
	write(I), write(' : '), affichage(C), nl,
	affichage(L).

affichageR([]).
affichageR([(I1, I2, R) | L]) :-
	write('<'), write(I1), write(', '), write(I2), write('> : '),
	write(R),nl,
	affichageR(L).

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2):-
    write("Etat de départ :"),nl,nl,
    affichage(Ls1),
    affichage(Lie1),
    affichage(Lpt1),
    affichage(Li1),
    affichage(Lu1),
    affichageR(Abr1),
    nl,nl,

    write("Etat d'arrivée :"),nl,nl,
    affichage(Ls2),
    affichage(Lie2),
    affichage(Lpt2),
    affichage(Li2),
    affichage(Lu2),
    affichageR(Abr2),
    nl,

    (test_clash(Ls2)->write('Il y a un clash. La branche est fermée.'); write('Pas de clash')),
    nl, nl.





%/* Démonstration */%

/* test_clash est vrai s'il y a un clash*/
test_clash(Ls):-member((I,C), Ls), cnamea(C), member((I,not(C)), Ls).


/* Résolution : renvoie vrai si 1 feuille est ouverte */
/*suit la boucle de contrôle du processus de développement de l'arbre p16*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr):- complete_some(Lie,Lpt,Li,Lu,Ls,Abr), \+ test_clash(Ls).
resolution([],Lpt,Li,Lu,Ls,Abr):- transformation_and([],Lpt,Li,Lu,Ls,Abr), \+ test_clash(Ls).
resolution([],Lpt,[],Lu,Ls,Abr):- deduction_all([],Lpt,[],Lu,Ls,Abr), \+ test_clash(Ls).
resolution([],[],[],Lu,Ls,Abr):- transformation_or([],[],[],Lu,Ls,Abr), \+ test_clash(Ls).
resolution([],[],[],[],Ls,Abr):- \+ test_clash(Ls).



/* boucle de résolution */
troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl,write('On a demontré la
                            proposition initiale !!!').