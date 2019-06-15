%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.
sat([],I,I):- write('SAT!!'), nl , !.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
append([Lit], I, R),
sat(CNFS,R,M).


%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% Si a la CNF només hi ha un literal, el segon parametre sera aquest literal
% En canvi, si hi ha més d'un, obtenim el primer de la llista, o bé el seu negat.
decideix(F, Lit):- member([Lit], F), !.
decideix([[Lit|_]|_], Lit).
decideix([[Lit|_]|_], LitNeg):- LitNeg is -Lit.

%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% Si tenim una CNF buida, parem.
simplif(_, [], []).
% Si trobem el literal dins la CNF, tallem i cridem recursivament a simplif, per buscar més literals a la CNF.
simplif(Lit, [CNF|CNFRES], CNFS) :- member(Lit, CNF),!, simplif(Lit, CNFRES, CNFS),!.
% Neguem el literal, i comparem aquest literal extrect amb l'inici de la CNF, si es el mateix tallem, i comparem que despres de
% treure'l no ens quedi la clausula buida []. Es torna a cridar a simplif recursivament amb el literal sense negar, la resta de la CNF,
% i acumulant el resultat a CNFS.
simplif(Lit, [CNF|CNFRES], CNFS):- 
    LitNeg is -Lit,
    append(A, [LitNeg|MS], CNF), !,
    append(A, MS, RES), RES \=[],
    simplif(Lit, CNFRES, CUACNFS),
    append([RES], CUACNFS, CNFS),!.
% Comprovem que la primera part de la CNF sigui una llista i cridem recursivament
simplif(Lit, [CNF|CNFRES], [CNFS|CNFSS]) :-  CNF = [_|_], simplif(Lit, CNF, CNFS), simplif(Lit, CNFRES, CNFSS), !.
% Comprovem que la primera part de la CNF NO sigui una llista i cridem recursivament, per tractar els literals.
simplif(Lit, [CNF|CNFRES], [CNF|CNFSS]) :- CNF \= [_|_], simplif(Lit, CNFRES, CNFSS), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% Com que L es una conjunció de disjuncions, per un parametre que sigui cert, tota la CNF ho sera, 
% per tant, retornem la mateixa CNF que ens han passat.
comaminimUn(L, L).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% Neguem tota la llista de variables, i generem la combinatoria de parelles, per satisfer que com a molt una, sigui certa.
comamoltUn([], []).
comamoltUn(L, CNF):- negat(L, NL), combina(NL, CNF).

% AUX
% negat(L, N).
% Donat una llista de variables booleans,
% -> el segon parametre sera una llista amb les variables negades.
negat([], []).
negat([L|LS], N):- L < 0, negat(LS, R), append([L], R, N), !.
negat([L|LS], N):- L > 0, LN is -L, negat(LS, R), append([LN], R, N).

% AUX
% combina(L, C).
% Donat una llista de variables booleanes.
% -> el segon parametre es una llista de parelles, obtenint totes les combinacions  [1,2,3] -> [1,2], [1,3], [2,3]
combina(L, C) :- findall(X0, combinaN(2, L, X0), C).

% AUX
% combinaN(N, L, R)
% Donat un numero N > 0, i una llista de variables booleanes, L
% El tercer parametre es una llista de N, amb les combinacions de L
combinaN(0,_,[]).
combinaN(N,L,[X|XS]) :- llistaN(X,L,R), N1 is N-1, combinaN(N1,R,XS).

% AUX
% llistaN(N, L, R).
% Donat un N (numero), i una llista L
% El tercer parametre R, retorna els elements sobrants de la llista a partir del valor de N.
llistaN(N,[N|L],R):- append(L, [], R).
llistaN(N,[_|L],R) :- llistaN(N,L,R).

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% Concatenació del resultat de comaminimUn, i comamoltUn.
exactamentUn(L, CNF):- comaminimUn(L, R), comamoltUn(L, S), append([R], S, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides
fesTauler(N, PI, PP, V, I):- fixa(PI, N, PR), prohibeix(PP, N, PPR), fesMatriu(N, V), append(PR, PPR, I).

% AUX
% fesMatriu(N, M)
% Donada una mida de matriu N,
% -> El segon parametre, sera una llista de llistes que representarà una matriu.
fesMatriu(N, M):- I is N*N, llista(1, I, R), trosseja(R, N, M).

% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
llista(F, F, [F]):- !.
llista(L, F, [L|LS]):- L =< F, N is L+1, llista(N, F, LS).

% AUX
% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
trosseja([], _, []).
trosseja(L, N, [LL|LS]):- length(LL, N), append(LL, R, L), trosseja(R, N, LS), !.

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
fixa(PS, N, F):- coordenadesAVars(PS, N, R), trosseja(R, 1, F), !.

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
prohibeix(PP, N, F):- coordenadesAVars(PP, N, R), negat(R, RN), trosseja(RN, 1, F), !.

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
% V es una matriu = [[1,2,3], [4,5,6], [7,8,9]], de 3 x 3 en aquest cas.
% Cridem a exactamentUn, per les files recursivament.
noAmenacesFiles([], []).
noAmenacesFiles([V|VS], F):- exactamentUn(V, FS), noAmenacesFiles(VS, R), append(FS, R, F).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
% Primer de tot transposem la matriu (intercanviem files x columnes), cridem a exactamentUn, i tornem a cridem a noAmenacesFiles,
% ja que com que tenim la matriu trasposada, les columnes son les files, i acumulem a la CNF.
noAmenacesColumnes([], []).
noAmenacesColumnes(V, C):- transposadaMatriu(V, [VS|VTS]), exactamentUn(VS, FS), noAmenacesFiles(VTS, R), append(FS, R, C), !.

% AUX
% transposadaMatriu(M, T).
% M es una matriu, (llista de llistes de variables = [[1,2,3], [4,5,6], [7,8,9]])
% -> El segon parametre T, serà la matriu M, trasposada, intercanvi de files per columnes
transposadaMatriu([[]|_], []).
transposadaMatriu(M, [T|TS]):- transposarColumna(M, T, RM), transposadaMatriu(RM, TS).

% AUX
% transposarColumna(M, F, MT).
% M es la matriu inicial, F, es la Fila transposada, i MT, la matriu resultant
% Transposa totes les columnes de la matiru M, recursivament, fins que la matriu es buida.
% Les columnes transposades es van acumulant a MT, formant la matriu transposta.
transposarColumna([], [], []).
transposarColumna([[H|MT]|F], [H|HS], [MT|MTS]):- transposarColumna(F, HS, MTS).

% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,D)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
% Es creen totes les diagonals d'una matriu N x N, es passen a llista de Variables, 
% i comprovem que no hi hagin amenaces en aquesta llista de VARS.
noAmenacesDiagonals(N,D):- diagonals(N,L), llistesDiagonalsAVars(L,N,VARS), noAmenacesDiagonalsVars(VARS,D).

% AUX
% noAmenacesDiagonalsVars(L, X).
% L es la llista de variables i X, es la llista de llistes de variables que conformen les diagonals.
% Cridem a comamoltUn, per assgurar que nomes hi haurà una reina en una diagonal, i cridem recursivament, per totes les diagonals.
noAmenacesDiagonalsVars([],[]).
noAmenacesDiagonalsVars([L|LS],X):- comamoltUn(L,D), noAmenacesDiagonalsVars(LS,R), append(D,R,X).

% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

% diagonalsIn(D,N,L)
% Generem les diagonals baix-esquerra a dalt-dreta, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...
diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

% Incrementa, la Fila i decrementar la Columna.
% fesDiagonal(F, C, LT).
% F es numero de fila, C el numero de columna, i LT serà la llista de tuples que codifiquen les diagonals de F i C.
fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).


% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
diagonals2In(D,N,[]):-D is 2*N,!.
diagonals2In(D,N,[L1|L]):- D<N,fesDiagonal2(N,D,L1), D1 is D+1, diagonals2In(D1,N,L).
diagonals2In(D,N,LS):- D>=N, F is D-N+1,fesDiagonalReves2(F,N,L1), D1 is D+1, diagonals2In(D1,N,L), append(L, [L1], LS).

% En comptes d'incrementar la Fila i decrementar la Columna, decrementem Fila i Columna.
% fesDiagonal2(F, C, LT).
% F es numero de fila, C el numero de columna, i LT serà la llista de tuples que codifiquen les diagonals de F i C.
fesDiagonal2(F,1,[(F,1)]):- !.
fesDiagonal2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonal2(F1,C1,R).

% quan la fila es 1 parem
fesDiagonalReves2(1,C,[(1,C)]):-!.
fesDiagonalReves2(F,C,[(F,C)|R]):-F1 is F-1, C1 is C-1, fesDiagonalReves2(F1,C1,R).

% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
%llistesDiagonalsAVars(Lparells,N,Lvars).
llistesDiagonalsAVars([], _, []).
llistesDiagonalsAVars([Lparells|LS],N,Lvars):- coordenadesAVars(Lparells, N, R), llistesDiagonalsAVars(LS, N, F), append([R], F, Lvars).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
minimNReines([], []).
minimNReines([V|VS], FN):- comaminimUn(V, CNF), minimNReines(VS, R), append([CNF], R, FN).

% AUX
% eliminaNegatius(M, X)
% M es la matriu a transformar.
% -> El segon parametre X, es la matriu resultant eliminant els numeros negatius.
eliminaNegatius([], []).
eliminaNegatius([M|MS], X):- M < 0, eliminaNegatius(MS, X).
eliminaNegatius([M|MS], [M|X]):- M > 0, eliminaNegatius(MS, X).


%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
resol():- 
    write("INTRODUEIX LA MIDA DEL TAULER"), nl,
    read(N),
    write("INTRODUEIX LA LLISTA DE POSICIONS PER A FIXAR "), nl ,
    read(I),
    write("INTRODUEIX LA LLISTA DE POSICIONS PER A PROHIBIR "), nl, 
    read(P),
    fesTauler(N, I, P, V, Ini),
    minimNReines(V, FN),
    append(Ini, FN, FN1),
    noAmenacesFiles(V, CNFfiles),
    append(CNFfiles, FN1, FN2),
    noAmenacesColumnes(V,CNFcolumnes),
    append(CNFcolumnes, FN2, FN3),
    noAmenacesDiagonals(N, CNFdiagonals),
    append(CNFdiagonals, FN3, R),
    sat(R,[],M),
    eliminaNegatius(M, MN),
    sort(0, @<, MN, MNS),
    mostraTauler(N, MNS), nl, fail.


%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
mostraTauler(0, []).
mostraTauler(N, L):- taulerRecursiu(1, N, N, L), mostrarRalleta(N), !.

% AUX
% taulerRecursiu(F, N, C, L).
% F es la fila actual a mostrar, N es valor màxim de la fila, C es la mida de la matriu, i L es la matriu a imprimir.
% De forma recursiva, va mostrant les reines per fila, desde el valor 1 fins a N, incrementant de N en N cada fila.
taulerRecursiu(_, _, _, []).
taulerRecursiu(F, F, F, _).
taulerRecursiu(F, N, C, [L|LS]):- mostrarRalleta(C), mostrarFilaN(F, N, L), F1 is N+C, F2 is N+1, taulerRecursiu(F2, F1, C, LS).

% AUX
% mostrarFilaN(F, N, L)
% F es el contador de la fila, N el valor màxim de la columna, N el valor de la matriu.
% Si L i F són el mateix, mostrem que hi ha una dama, altrament mostrem un espai en blanc.
% Al arribar al final de la matriu, mirem si la Fila la Columna i el Valor son el mateix, i imprimim Q.
mostrarFilaN(N, N, N):- write('|Q|'), nl, !.
mostrarFilaN(N, N, _):- write('| |'), nl, !.
mostrarFilaN(F, N, F):- write('|Q'), FN is F + 1, mostrarFilaN(FN, N, F).
mostrarFilaN(F, N, L):- write('| '), FN is F + 1, mostrarFilaN(FN, N, L).

% AUX
% mostrarRalleta(C)
% C es la mida de la matriu.
% Conté la formula per mostrar les ralletes necessaries. (3*2N-1)
mostrarRalleta(C):- R is C-1, R1 is 2*R, R2 is 3 + R1, mostraRalletaRec(R2), nl.

% AUX
% mostraRalletaRec(N)
% N es le numero de Ralletes '-', a mostrar per pantalla.
mostraRalletaRec(0).
mostraRalletaRec(N):- write("-"), N1 is N-1, mostraRalletaRec(N1).