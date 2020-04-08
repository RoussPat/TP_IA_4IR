%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de façon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Pu (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Pu
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPu, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier
:- set_prolog_stack(global, limit(1 000 000 000 000)).
:- set_prolog_stack(trail,  limit(200 000 000 000)).
:- set_prolog_stack(local,  limit(200 000 000 000)).

%*******************************************************************************

%*************************************************
%	Affichage de la solution : affiche_solution
%*************************************************

% Cas trivial
affiche_solution(IS,_Q,IS,N) :-
	write("Reussit en : "),
	write(N),
	write("\n"), 
    !.

% Si l'etat a deja ete developpe
affiche_solution(U,Q,IS,N) :-
    %U /= IS,
    belongs([U,[_,_,_],Pere,A],Q),
    affiche_solution(Pere,Q,IS,N),
    write(A),
    write(" -> ").


%************************************************************
%	Determination des successeurs d'une situation et de leur
%   évalution : expand 
%************************************************************
expand(U,S,[_Fu,_Hu,Gu],[Fs,Hs,Gs],A,FS) :-
    rule(A,Cost,U,S),
    Gs is Gu+Cost,
    heuristique(S,Hs,FS),
    Fs is Gs + Hs.

% Remarque : cette solution permet de trouver 1 successeur, il faut donc utiliser le prédicat findall/3 pour trouver tous les successeurs dans aetoile/3.
/*
 Une alternative serait pour utiliser expand/4 directement dans aetoile/3 :
	
expand(Ls, U, [_,_,G]):- 
	findall([S,[Fs,Hs,Gs],U,Act],
			(rule(A,Cost,U,S), heuristique(S,Hs), Gs is G+Cost, Fs is Gs+Hs),
		 	Ls).
*/


%*********************************************************
%	Traitement des noeuds successeurs : loop_successors
%*********************************************************

loop_successors([],Pui,Pfi,Puf,Pff,_Q) :-
    Puf = Pui,
    Pff = Pfi.

loop_successors([[S,[Fs,Hs,Gs],U,A]|Rest],Pui,Pfi,Puf,Pff,Q):-
    % Si S est dans Q (deja developpe), on oublie cet etat
    (belongs([S,_,_,_],Q)->
        Puaux = Pui,
        Pfaux = Pfi
    ;
		% Si S est dans Pu, on garde le terme associe a la meilleure evaluation (dans Pu et Pf)
        (suppress([S,[Fs1,Hs1,Gs1],_OldPere,_OldA],Pui,Put)->
            ([Fs,Hs,Gs] @< [Fs1,Hs1,Gs1] ->
                suppress([[Fs1,Hs1,Gs1],S],Pfi,Pft),
                insert([[Fs,Hs,Gs],S],Pft,Pfaux),
                insert([S,[Fs,Hs,Gs],U,A],Put,Puaux)   
            ; %else
            Puaux = Pui,
            Pfaux = Pfi
            )
        ; 
		% Sinon on cree un nouveau terme a inserer dans Pu (et Pf)
        insert([[Fs,Hs,Gs],S],Pfi,Pfaux),
        insert([S,[Fs,Hs,Gs],U,A],Pui,Puaux)
        )
    ),
    loop_successors(Rest,Puaux,Pfaux,Puf,Pff,Q).
    

%*******************************************************************************

%*******************
%	Algorithme A*
%*******************

% Cas trivial : Pf et Pu sont vides
aetoile(Pf,Pu,_,_IS,_FS,N) :-
    empty(Pf),
    empty(Pu),
    write("Echec en : "),
	write(N),
	write("\n"),
    writeln("PAS DE SOLUTION: L'ETAT FINAL N'EST PAS ATTEIGNABLE !").

%Cas trivial : le noeud minimal de Pf correspond a la situation finale
aetoile(Pf,Pu,Q,IS,FS,N) :-
    suppress_min([[Ff,Hf,Gf],FS],Pf,_Pf1),
    suppress([FS,[Ff,Hf,Gf],Pere,Au],Pu,_Pu1),
    insert([FS,[Ff,Hf,Gf],Pere,Au],Q,Q1), % insert dans Q pour que l'affichage soit plus simple
    affiche_solution(FS,Q1,IS,N).    

% Cas general
aetoile(Pf,Pu,Q,IS,FS,N) :-
    suppress_min([[Fu,Hu,Gu],U],Pf,Pf1),
    suppress([U,[Fu,Hu,Gu],Pere,Au],Pu,Pu1),
    write("["), 
	write(Fu), 
	write(","), 
	write(Hu), 
	write(","), 
	write(Gu), 
	write("]"),    
    write_state(U),
    
    findall([S,[Fs,Hs,Gs],U,A_new],
			(expand(U,S,[_,_,Gu],[Fs,Hs,Gs],A_new, FS)),
			LS),
    loop_successors(LS,Pu1,Pf1,Pu2,Pf2,Q),    
    insert([U,[Fu,Hu,Gu],Pere,Au],Q,Q1),
	NewN is N+1,
    aetoile(Pf2,Pu2,Q1,IS,FS,NewN).


%*******************************************************************************

%***********
%	Main
%***********
main :-
	initial_state1(IS),
	final_state3x3(FS),
	main2(IS,FS).


main2(IS,FS) :-
	% Situation initiale est IS

	% Calcul de F0, H0, G0 pour cette situation
    heuristique(IS,H0,FS),
    G0 is 0,
    F0 is H0 + G0,

	% Initialisations Pf, Pu et Q 
    Pf = nil,
    Pu =nil,
    Q = nil,

	% Insertion des noeuds dans Pf et Pu
    insert([[F0,H0,G0],IS],Pf,Pf1),
    insert([IS,[F0,H0,G0],nil,nil],Pu,Pu1),

	% Lancement de Aetoile
    aetoile(Pf1,Pu1,Q,IS,FS,0).
	
%*******************************************************************************

%*************************
%	Tests de performance
%*************************

testheuristique :-
	initial_state1(IS1), %3x3
	initial_state2(IS2), %3x3
	initial_state3(IS3), %3x3
	initial_state4(IS4), %3x3
	initial_state5(IS5), %3x3
	initial_state6(IS6), %3x3 non connex
	initial_state7(IS7), %4x4 trop lourd
	initial_state8(IS8), %4x4 
	final_state3x3(FS3), %3x3
	final_state4x4(FS4), %4x4

	write("IS1 : "),
	write(IS1),
	write(" Heuristique 1 :"),
	heuristique1(IS1,H11,FS3),
	write(H11),
	write(" Heuristique 2 :"),
	heuristique2(IS1,H21,FS3),
	write(H21),
	write("\n"),

	write("IS2 : "),
	write(IS2),
	write(" Heuristique 1 :"),
	heuristique1(IS2,H12,FS3),
	write(H12),
	write(" Heuristique 2 :"),
	heuristique2(IS1,H22,FS3),
	write(H22),
	write("\n"),

	write("IS3 : "),
	write(IS3),
	write(" Heuristique 1 :"),
	heuristique1(IS3,H13,FS3),
	write(H13),
	write(" Heuristique 2 :"),
	heuristique2(IS3,H23,FS3),
	write(H23),
	write("\n"),

	write("IS4 : "),
	write(IS4),
	write(" Heuristique 1 :"),
	heuristique1(IS4,H14,FS3),
	write(H14),
	write(" Heuristique 2 :"),
	heuristique2(IS4,H24,FS3),
	write(H24),
	write("\n"),

	write("IS5 : "),
	write(IS5),
	write(" Heuristique 1 :"),
	heuristique1(IS5,H15,FS3),
	write(H15),
	write(" Heuristique 2 :"),
	heuristique2(IS5,H25,FS3),
	write(H25),
	write("\n"),

	write("IS6 : "),
	write(IS6),
	write(" Heuristique 1 :"),
	heuristique1(IS6,H16,FS3),
	write(H16),
	write(" Heuristique 2 :"),
	heuristique2(IS6,H26,FS3),
	write(H26),
	write("\n"),

	write("IS7 : "),
	write(IS7),
	write(" Heuristique 1 :"),
	heuristique1(IS7,H17,FS4),
	write(H17),
	write(" Heuristique 2 :"),
	heuristique2(IS7,H27,FS4),
	write(H27),
	write("\n"),

	write("IS8 : "),
	write(IS8),
	write(" Heuristique 1 :"),
	heuristique1(IS8,H18,FS4),
	write(H18),
	write(" Heuristique 2 :"),
	heuristique2(IS8,H28,FS4),
	write(H28),
	write("\n").


performance :-
	initial_state1(IS1), %3x3
	initial_state2(IS2), %3x3
	initial_state3(IS3), %3x3
	initial_state4(IS4), %3x3
	initial_state5(IS5), %3x3
	initial_state6(IS6), %3x3 non connex
	initial_state7(IS7), %4x4 trop lourd
	initial_state8(IS8), %4x4 
	final_state3x3(FS3), %3x3
	final_state4x4(FS4), %4x4
    statistics(runtime, [Start1,_]),
    main2(IS1,FS3),
    statistics(runtime, [Stop1,_]),
    Runtime1 is Stop1 - Start1, % resultat en ms
	write("\nIS1 : "),
	write(Runtime1),
	write("\n"),
	statistics(runtime, [Start2,_]),
	main2(IS2,FS3),
    statistics(runtime, [Stop2,_]),
    Runtime2 is Stop2 - Start2, % resultat en ms
	write("\nIS2 : "),
	write(Runtime2),
	write("\n"),
	statistics(runtime, [Start3,_]),
	main2(IS3,FS3),
    statistics(runtime, [Stop3,_]),
    Runtime3 is Stop3 - Start3, % resultat en ms
	write("\nIS3 : "),
	write(Runtime3),
	write("\n"),
	statistics(runtime, [Start4,_]),
	main2(IS4,FS3),
    statistics(runtime, [Stop4,_]),
    Runtime4 is Stop4 - Start4, % resultat en ms
	write("\nIS4 : "),
	write(Runtime4),
	write("\n"),
	statistics(runtime, [Start5,_]),
	main2(IS5,FS3),
    statistics(runtime, [Stop5,_]),
    Runtime5 is Stop5 - Start5, % resultat en ms
	write("\nIS5 : "),
	write(Runtime5),
	write("\n"),
	statistics(runtime, [Start8,_]),
	main2(IS8,FS4),
    statistics(runtime, [Stop8,_]),
    Runtime8 is Stop8 - Start8, % resultat en ms
	write("\nIS8 : "),
	write(Runtime8),
	write("\n"),
	statistics(runtime, [Start6,_]),
	main2(IS6,FS3),
    statistics(runtime, [Stop6,_]),
    Runtime6 is Stop6 - Start6, % resultat en ms
	write("\nIS6 : "),
	write(Runtime6),
	write("\n"),
	statistics(runtime, [Start7,_]),
	main2(IS7,FS4),
    statistics(runtime, [Stop7,_]),
    Runtime7 is Stop7 - Start7, % resultat en ms
	write("\nIS7 : "),
	write(Runtime7),
	write("\n").


%**********************
%	Tests unitaires
%**********************
	
% Test expand/4 sur la situation initiale
test_loop_successors :-
	initial_state1(IS1), %3x3
	initial_state2(IS2), %3x3
	initial_state3(IS3), %3x3
	final_state3x3(FS3), %3x3

	write("IS1 : "),
	write(IS1),
	write("\nExpands :"),
	test_expands2(LS1,IS1,FS3),
	write(LS1),
	write("\nloops successors :"),
		test_loop_successors2(LS1,Pu1,Pf1,Q1,IS1,FS3),
	write("\n Pu :"),write(Pu1), write("\n Pf"), write(Pf1),write("\n Q:"), write(Q1),
	write("\n"),
		
	write("IS2 :"),
	write(IS2),
	write("\nExpands :"),
	test_expands2(LS2,IS2,FS3),
	write(LS2),
	write("\nloops successors :"),
		test_loop_successors2(LS2,Pu2,Pf2,Q2,IS2,FS3),
	write("\nPu :"),write(Pu2), write("\nPf"), write(Pf2),write("\nQ:"), write(Q2),
	write("\n"),

	write("IS3 :"),
	write(IS3),
	write("\nExpands :"),
	test_expands2(LS3,IS3,FS3),
	write(LS3),
	write("\nloops successors :"),
		test_loop_successors2(LS3,Pu3,Pf3,Q3,IS3,FS3),
	write("\nPu :"),write(Pu3), write("\nPf"), write(Pf3),write("\nQ:"), write(Q3),
	write("\n").
		

test_loop_successors2(LS,Pu2,Pf2,Q,IS,FS) :-
    heuristique(IS,H0,FS),
    G0 is 0,
    F0 is H0 + G0,
    Pf = nil,
    Pu =nil,
    Q = nil,
    insert([[F0,H0,G0],IS],Pf,Pf1),
    insert([IS,[F0,H0,G0],nil,nil],Pu,Pu1),

    findall([S,[Fs,Hs,Gs],IS,A],expand(IS,S,[F0,H0,G0],[Fs,Hs,Gs],A,FS),LS),
    loop_successors(LS,Pu1,Pf1,Pu2,Pf2,Q).


test_expands  :-
	initial_state1(IS1), %3x3
	initial_state2(IS2), %3x3
	initial_state3(IS3), %3x3
	final_state3x3(FS3), %3x3

	write("IS1 : "),
	write(IS1),
	write(" Expands :"),
	test_expands2(LS1,IS1,FS3),
	write(LS1),
	write("\n"),
		
	write("IS2 : "),
	write(IS2),
	write(" Expands :"),
	test_expands2(LS2,IS2,FS3),
	write(LS2),
	write("\n"),

	write("IS3 :"),
	write(IS3),
	write(" Expands :"),
	test_expands2(LS3,IS3,FS3),
	write(LS3),
	write("\n").

test_expands2(LS,IS,FS) :-
    heuristique(IS,H0,FS),
    G0 is 0,
    F0 is H0 + G0,

    findall([S,[Fs,Hs,Gs],IS,A],expand(IS,S,[F0,H0,G0],[Fs,Hs,Gs],A,FS),LS).


/* A VOIR SI ON GARDE (javais ca dans mon code)




%Test sur la situation finale
test_expand2(S_list) :-
	final_state(U),
	heuristique(U,H),
	G=0,
	F is G+H,
	findall([S, Val_new, U, A], (expand(U, S, [F,H,G], Val_new, A)), S_list).

%LOOP_SUCCESSORS

test_ls(S_list, Pu_new, Pf_new, Q) :-
	initial_state(U),
	heuristique(U,H),
	G=0,
	F is G+H,
	Pf = nil,
	Pu = nil,
	Q = nil,
	insert([[F,H,G], U], Pf, Pf_new),
	insert([U, [F,H,G], nil, nil], Pu, Pu_new),	
	%expand(S_list,U,[F,H,G]).
	findall([S, Val_new, U, A], (expand(U, S, [F,H,G], Val_new, A)), S_list),
	loop_successors(S_list, Pu, Pf, Q, Pu_new, Pf_new).


%AFFICHE_SOLUTION

test_affiche :- 
	G= nil,
	insert(1, G, G1),
	insert(3, G1, G2),
	insert(4, G2, G3),
	insert(8, G3, G4),
	insert(6, G4, G5),	
	insert(2, G5, G6),
	put_flat(G6).

*/
   
