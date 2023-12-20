/* Fonctions données dans l'énoncé */

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).


compteur(1).
genere(Nom) :- compteur(V),nombre(V,L1),
                concat([105,110,115,116],L1,L2),
                V1 is V+1,
                dynamic(compteur/1),
                retract(compteur(V)),
                dynamic(compteur/1),
                assert(compteur(V1)),nl,nl,nl,
                name(Nom,L2).


nombre(0,[]).
nombre(X,L1) :- R is (X mod 10),
                Q is ((X-R)//10),
                chiffre_car(R,R1),
                char_code(R1,R2),
                nombre(Q,L),
                concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).


compteur(1).
genere(Nom) :- compteur(V),nombre(V,L1),
                concat([105,110,115,116],L1,L2),
                V1 is V+1,
                dynamic(compteur/1),
                retract(compteur(V)),
                dynamic(compteur/1),
                assert(compteur(V1)),nl,nl,nl,
                name(Nom,L2).


nombre(0,[]).
nombre(X,L1) :- R is (X mod 10),
                Q is ((X-R)//10),
                chiffre_car(R,R1),
                char_code(R1,R2),
                nombre(Q,L),
                concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').





/* Partie 1 */


:- discontiguous concept/1.

% Vérification sémantique                
concept(C) :- cnamea(C). % concepts atomique
concept(CG) :- cnamena(CG). % non atomique
instance(I) :- iname(I). % identificateurs d instance
role(R) :- rname(R). % identificateurs de rôle.


% la grammaire de  ALC 
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).


% Vérification syntaxique Tbox et Abox concept et role   

definition(CA, CG) :- cnamena(CA), concept(CG).

verify_tbox([]).
verify_tbox([(CA, CG) | Q]) :-  definition(CA, CG), verify_tbox(Q).


instanciationC(I, CG) :- instance(I), concept(CG).
instanciationR(I1, I2, R) :- instance(I1), instance(I2), role(R).
verify_aboxConcept([]).
verify_aboxConcept([(I, CG) | Q]) :- instanciationC(I, CG), verify_aboxConcept(Q).
verify_aboxRole([]).
verify_aboxRole([(I1, I2, R) | Q]) :- instanciationR(I1, I2, R), verify_aboxRole(Q).
verif_Abox(AboxC,AboxR) :- verify_aboxConcept(AboxC), verify_aboxRole(AboxR).


% Auto-référencement                       
non_circular([]).
non_circular([C|L]) :- equiv(C, Def_C), autoref(C, Def_C), non_circular(L).

autoref(_, Def) :- cnamea(Def).
autoref(C, Def) :- C \== Def, cnamena(Def), equiv(Def, Def_developpe), autoref(C, Def_developpe).
autoref(C, and(D1,D2)) :- autoref(C, D1), autoref(C, D2).
autoref(C, or(D1,D2)) :- autoref(C, D1), autoref(C, D2).
autoref(C, all(_,D)) :- autoref(C,D).
autoref(C, some(_,D)) :- autoref(C,D).
autoref(C, not(D)) :- autoref(C,D).
	

% Traitement des Boxs 
developpe(C, C) :- cnamea(C).
developpe(C, D) :- equiv(C, E), developpe(E, D).
developpe(not(C), not(D)) :- developpe(C, D).
developpe(or(C1,C2), or(D1,D2)) :-  developpe(C1, D1),  developpe(C2, D2).
developpe(and(C1,C2),and(D1,D2)) :-  developpe(C1,D1), developpe(C2,D2).
developpe(some(R,C), some(R,D)) :- developpe(C, D).
developpe(all(R,C), all(R,D)) :- developpe(C, D).


% traitement de Tbox et traitement de Abox
transforme([], []).
transforme([(X,C) | L], [(X,D) | M]) :-  developpe(C, E), nnf(E, D), transforme(L, M).


nnf(not(and(C1,C2)),or(NC1,NC2)) :- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)) :- nnf(not(C1),NC1),nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)) :- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)) :- nnf(not(C),NC),!.
nnf(not(not(X)),X) :- !.
nnf(not(X),not(X)) :- !.
nnf(and(C1,C2),and(NC1,NC2)) :- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)) :- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)) :-nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :-  nnf(C,NC),!.
nnf(X,X).








/* Partie 2 */


% Acquisition des propositions de type 1

acquisition_prop_type1(Abi, Abi1, Tbox) :- 
    write('I ='),nl, 
    read(I), writef('I : %w', [I]), nl, nl,
    write('C = '),nl, 
    read(CG), writef('C : %w', [C]), nl, nl,
    (instanciationC(I, CG) -> % if 
        writef('%w : %w', [I, CG])
        ; ( % else
        write('\[ERREUR] : I est pas déclaré ou C est pas un concept'), nl,
        write('A nouveau'), nl, fail
    )),
    transforme([(I,not(CG))], [(I, CG_dev_nnf)]), % Développement + nnf
    concat(Abi,[(I, CG_dev_nnf)], Abi1), % Ajout de l input  dans la ABox
    %write("Abi1"), write(Abi1),
    nl. 




% Acquisition des propositions de type 2

acquisition_prop_type2(Abi, Abi1, Tbox) :- 
   read(C1), nl, writef('C1 = %w', [C1]), nl, nl,
    write('C2 = '), nl, 
    read(C2),nl, writef('C2 = %w', [C2]), nl, nl,
    (concept(and(C1, C2)) -> % if 
        writef("%w ⊓ %w ⊑ ⊥", [C1, C2])
        ; ( % else
        write('[ERREUR] : C1 ou C2 est pas déclaré'), nl,
        write('A nouveau'), nl, fail
    )),
    genere(Random_CName),
    transforme([(Random_CName, and(C1, C2))], [(Random_CName, and(C1_dev_nnf, C2_dev_nnf))]),
    concat(Abi, [(Random_CName, and(C1_dev_nnf, C2_dev_nnf))], Abi1), % Ajout de l input dans la ABox
    %write("Abi1"), write(Abi1),
    nl.







/* Partie 3 */

:- encoding(utf8).

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
    write("On applique la règle  \u2294 sur "), affichage([(A,or(C,D))]), write("- première branche"),nl,
    affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(A,or(C,D)) | Lu], Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),

    % continue la résolution de la première branche
    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr).


transformation_or(Lie, Lpt, Li, [(A,or(C,D)) | Lu], Ls, Abr):-
    % ajoute assertion a : D à la deuxième branche
    evolue((A, D), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),

    % affichage
    nl,
    write("On applique la règle  \u2294 sur "), affichage([(A,or(C,D))]), write("- deuxième branche"),nl,
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











premiere_etape(Tbox, Abi, Abr) :-
    setof((CA, CG), equiv(CA, CG), Tboxt),      
    setof((I1, I2), inst(I1, I2), Abit),        
    setof((I1, I2, R), instR(I1, I2, R), Abr), 
    (verif_Tbox(Tboxt) ->
        write('[LOG] Vérification de la TBox réussi'), nl;
        write('[ERREUR] Il y a erreur de syntaxe dans la TBox'), nl, halt),
    
    % Vérification de la Abox
    (verif_Abox(Abit,Abr) ->
        write('[LOG] Vérification de la ABox réussi'), nl;
        write('[ERREUR] Il y a erreur de syntaxe dans la ABox'), nl, halt),
    
    % Vérification des auto-référencements
    setof(X, cnamena(X), Lcc),    % Récupération de la liste des concepts non atomiques
    (verif_Autoref(Lcc) ->
        write('[LOG] Il n\'y a pas auto-référencement dans la TBox'), nl ;
        write('[ERREUR] Il y a auto-référencement dans la TBox'), nl, halt),

    transforme(Abit, Abi),
    %write('abi:'), write(Abi), nl,
    %write('abit:'), write(Abit),nl,
    transforme(Tboxt, Tbox),
    %write('Tbox:'), write(Tbox), nl,
    %write('Tboxt:'), write(Tboxt),nl,
    write('[LOG] Transformation finie'),nl.

deuxieme_etape(Abi,Abi1,Tbox) :-
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl,
    write('Entrez le numéro du type de proposition que vous voulez démontrer :'), nl,
    write('1 Une instance donnée appartient a un concept donné.'), nl,
    write('2 Deux concepts qui n\'ont pas d\'éléments en commun (ils ont une intersection vide).'), nl,
    read(R),
    suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox), !.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox), !.
suite(_,Abi,Abi1,Tbox) :- nl, 
    write('réponse incorrecte.'), nl,
    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

troisieme_etape(Abi,Abr) :-
    tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
    write('==='),nl,nl,
    resolution(Lie,Lpt,Li,Lu,Ls,Abr).

projet :-
    load_files('T-abox_tbox.pl'),
    premiere_etape(Tbox, Abi, Abr),
    deuxieme_etape(Abi,Abi1,Tbox),
    (troisieme_etape(Abi1,Abr)->
    	write('Il y a une feuille ouverte du coup on n\'a pas pu démontré la proposition');
    	write('Toutes les feuilles sont fermées donc on a bien démontré la proposition')),nl.

projet.