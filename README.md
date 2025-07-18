# Tesina de Licenciatura en Sistemas  
**Autor:** Germán Costilla

Este repositorio contiene los modelos matemáticos desarrollados para la tesina de Licenciatura en Sistemas, centrada en la generación de fixtures utilizando programación lineal entera.

## Estructura del repositorio

Los directorios se agrupan por cantidad de equipos del fixture, y en cada directorio se encuentran:

- **Modelo base con patrones de localía (home/away patterns)**  
- **Modelo extendido con restricciones de clustering**  
- **Modelo extendido adaptado al fixture de la Superliga Argentina 2018/2019**

## Input

Los modelos utilizan archivos de entrada que deben ser provistos en el mismo directorio del modelo:

- `pattern.txt`:  
  Cada línea representa un patrón de localía (home/away pattern).  
  **Nota:** el modelo utiliza exactamente la cantidad de patrones definidos en este archivo.

- `breaksByPattern.txt`:  
  Cada línea indica la cantidad de *breaks* que contiene el patrón correspondiente.

- `localitiesByPattern.txt`:  
  Cada línea indica si el patrón `j` tiene localía en la fecha `f`.

## Output

Los resultados de la ejecución de los modelos se encuentran organizados según el solver utilizado:

- **NEOS/**  
  Contiene los resultados obtenidos con el solver **Gurobi**, ejecutado mediante el servicio [NEOS Server](https://neos-server.org).

- **Archivos fuera del directorio NEOS**  
  Corresponden a ejecuciones locales con el solver **CPLEX**.


