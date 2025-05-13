#Patrones
set patterns := {read "../solver_input/patterns28.txt" as "<1n,2n,3n,4n,5n,6n,7n,8n,9n,10n,11n,12n,13n,14n,15n,16n,17n,18n,19n,20n,21n,22n,23n,24n,25n,26n,27n>"};

#11, 6, 6, 5

#34.6
set capital := {1 .. 11};
#23.1
set bs_as := {12 .. 17};
#23.1
set pampa := {18 .. 23};
#19.2
set noa := {24 .. 28};

#Cantidad de patrones
param J := card(patterns);
set patrones := {1 .. J};

#Cantidad de breaks por patron
param breaks[patrones] := read "../solver_input/breaksByPattern28.txt" as "<1n> 2n";

#Cantidad de equipos
param I := 28;
set equipos := {1 .. I};

#Cantidad de clusters
set clusters := {1 .. 4};

set equipo_numero_cluster[equipos] := <1> {1}, <2> {1}, <3> {1}, <4> {1}, <5> {1}, <6> {1}, <7> {1}, <8> {1}, <9> {1}, <10> {1}, <11> {1}, <12> {2}, <13> {2}, <14> {2}, <15>{2}, <16> {2}, <17> {2}, <18> {3}, <19> {3}, <20> {3}, <21> {3}, <22> {3}, <23> {3}, <24> {4}, <25> {4}, <26> {4}, <27> {4}, <28> {4};


set equipo_cluster := equipos * clusters;
#Cantidad de fechas
set fechas:= {1 .. I-1};

#Cantidad de partidos por fecha
param P_F := I/2;

#Equipo-Patron
set equipo_patron := equipos * patrones;

#Local-Visitante
set local_visitante := {<e1, e2> in equipos * equipos with e1 != e2};

#Local-Visitante-Fecha
set local_visitante_fecha := local_visitante * fechas;

#Local-Fecha
set local_fecha := equipos * fechas;
set equipo_fecha := local_fecha; #Es solo un renombre que me sirve para poder leer la restriccion

#Localia en fecha: 1 Si el patrón j da localía en la fecha f. 0 caso contrario, con j entre {1...J}, y f entre {1...F} 
set patron_fecha := patrones * fechas;
param home[patron_fecha] := read "../solver_input/localitiesByPattern28.txt" as "<1n,2n> 3n"; 

# 'Funcion' que dado un numero de cluster devuelve a los equipos en el
set cluster_equipos[clusters] := <1> { 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}, <2> {12, 13, 14, 15, 16, 17}, <3> {18, 19, 20, 21, 22, 23}, <4> {24, 25, 26, 27, 28};
set without_local_cluster := (cluster_equipos[1] * {<2>, <3>, <4>}) union (cluster_equipos[2] * {<1>, <3>, <4>}) union (cluster_equipos[3] * {<1>, <2>, <4>}) union (cluster_equipos[4] * {<1>, <2>, <3>});

# Variables -------------------------------------------------------------------------------------------

#1 Si elijo el patron j, 0 en caso contrario
var P[patrones] binary;

#1 Si le asigno al equipo i el patron j
var X[equipo_patron] binary;

#1 Si el equipo x juega contra el equipo y en la fecha z
var F[local_visitante_fecha] binary;

#1 Si el equipo i juega de local en la fecha f
var L[local_fecha] binary;

#Cantidad de partidos del equipo i como visitante del cluster j
var VC[without_local_cluster] integer;

#Cantidad de partidos del equipo i como local del cluster j
var LC[without_local_cluster] integer;

# Objetivo --------------------------------------------------------------------------------------------
# Quedarse con los patrones que tengan menos breaks tal que generen un fixture valido
minimize breaks:
    sum <j> in patrones: breaks[j] * P[j];

# Subject to -------------------------------------------------------------------------------------------

#Me quedo con tantos patrones como equipos tenga
subto cant_patrones_igual_cant_equipos:
    sum <j> in patrones: P[j] == I;

#Le asigno exactamente un patrón a cada equipo
subto patron_asignado_equipo:
    forall<i> in equipos do
        sum <j> in patrones: X[i,j] == 1;

subto patron_asignado_sin_repetir:
    forall<j> in patrones do
        sum<i> in equipos: X[i,j]  <= 1;

subto patron_asignado_valido:
    forall<i> in equipos do
        forall<j> in patrones do
            X[i,j] <= P[j];

#La localía del equipo i en la fecha f queda determinada por el patrón que se haya elegido
subto localia_equipo_fecha:
    forall<i> in equipos do
        forall<f> in fechas do
            sum <j> in patrones: X[i,j] * home[j,f] == L[i,f];

#Si el equipo x juega contra el equipo y en alguna fecha, no tiene que volver a jugar con ese equipo en las demás fechas. 
subto fixture: 
    forall<l,v> in local_visitante do
        sum <f> in fechas: F[l,v,f] +  sum <f> in fechas: F[v,l,f] == 1;

#La fecha con el equipo i es valida si y solo si ese equipo tiene un patron asignado que de localia en esa fecha
#Ligo las variables
subto patron_localica:
    forall<l,f> in equipo_fecha do
        sum <v> in equipos - {l}: F[l,v,f] == L[l, f];

#Si el equipo x juega contra el equipo y en una fecha, no puede jugar contra otro equipo y’ en la misma fecha.
subto un_partido_por_fecha:
    forall<x,z> in equipo_fecha do
        sum <y> in equipos - {x}: (F[x,y,z] + F[y,x,z]) == 1;

#----------------------- Restricciones de clusterizacion --------------------------------

#Cuento la cantidad de partidos que juega el equipo i en el cluster j de visitante
subto cantidad_partidos_cluster_visitante:
    forall<i> in equipos do
        forall <j> in clusters - {equipo_numero_cluster[i]} do
            sum <e,f> in cluster_equipos[j] * fechas: F[e,i,f] == VC[i,j];

#La anterior restriccion determina la cantidad de partidos de local del equipo i contra equipos del cluster j
subto cantidad_partidos_cluster_visitante_local:
    forall<i> in equipos do
        forall <j> in clusters - {equipo_numero_cluster[i]}: 
            card(cluster_equipos[j]) - VC[i,j] == LC[i, j];

#Cada equipo tiene que jugar exactamente una vez contra cada equipo de un cluster j
subto cantidad_partidos:
    forall<i> in equipos do
        forall <j> in clusters - {equipo_numero_cluster[i]}: 
            card(cluster_equipos[j]) == VC[i,j] + LC[i,j];

subto fairness_cluster:
        forall<i> in equipos do
            forall <j> in clusters - {equipo_numero_cluster[i]}:
                VC[i,j] - LC[i,j] <= 1 and
                LC[i,j] - VC[i,j] <= 1;
