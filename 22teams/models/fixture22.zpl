#Patrones
set patterns := {read "../solver_input/patterns22.txt" as "<1n,2n,3n,4n,5n,6n,7n,8n,9n,10n,11n,12n,13n,14n,15n,16n,17n,18n,19n,20n,21n>"};

#Cantidad de patrones
param J := card(patterns);
set patrones := {1 .. J};

#Cantidad de breaks por patron
param breaks[patrones] := read "../solver_input/breaksByPattern22.txt" as "<1n> 2n";

#Cantidad de equipos
param I := 22;
set equipos := {1 .. I};

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
param home[patron_fecha] := read "../solver_input/localitiesByPattern22.txt" as "<1n,2n> 3n"; 

# Variables -------------------------------------------------------------------------------------------

#1 Si elijo el patron j, 0 en caso contrario
var P[patrones] binary;

#1 Si le asigno al equipo i el patron j
var X[equipo_patron] binary;

#1 Si el equipo x juega contra el equipo y en la fecha z
var F[local_visitante_fecha] binary;

#1 Si el equipo i juega de local en la fecha f
var L[local_fecha] binary;

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

#La fecha con el equipo i es valida si y solo si ese equipo tiene un patron asignado que de localia en esa fecha
#Ligo las variables
subto patron_localica:
    forall<l,f> in equipo_fecha do
        sum <v> in equipos - {l}: F[l,v,f] == L[l, f];

#La localía del equipo i en la fecha f queda determinada por el patrón que se haya elegido
subto localia_equipo_fecha:
    forall<i> in equipos do
        forall<f> in fechas do
            sum <j> in patrones: X[i,j] * home[j,f] == L[i,f];

#Si el equipo x juega contra el equipo y en alguna fecha, no tiene que volver a jugar con ese equipo en las demás fechas. 
subto fixture: 
    forall<x,y> in local_visitante do
        sum <z> in fechas: F[x,y,z] +  sum <z> in fechas: F[y,x,z] == 1;

#Si el equipo x juega contra el equipo y en una fecha, no puede jugar contra otro equipo y’ en la misma fecha.
subto un_partido_por_fecha:
    forall<x,z> in equipo_fecha do
        sum <y> in equipos - {x}: (F[x,y,z] + F[y,x,z]) == 1;

