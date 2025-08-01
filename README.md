# Mixture preparation plant

## Materials for paper:
M. V. Neyzov and E. V. Kuzmin.
Application of the Signals Perspective in Development and Verification of the Industrial Plant Control Program // Programming. 2025

## Resume

Control Object – Mixture preparation plant.

Control Device – **`PLC`** (Programmable Logic Controller).

Task 1 – Development and verification of the plant control model.

Task 2 – Transforming a model into a control program.

[//]:----------------------------------------------------

## Technology Stack

Specification Language: **`TLA+`**

Model Checker Tool: **`TLC`**

Object Oriented Programming Language: **`ST`** (Structured Text) IEC 61131-3:2025

IDE: **`CoDeSys`** v3.5

[//]:----------------------------------------------------

## Content

* Control Model
    * TLA+ specification [module set](./TLA+_specification)
    * Main module [mixture.tla](./TLA+_specification/mixture.tla)
* Control Program
    * ST code [unit set](./ST_code)
    * Program [PLC_PRG.st](./ST_code/PLC_PRG.st)
    * Main unit [ControlModel.st](./ST_code/ControlModel.st)

[//]:----------------------------------------------------

## Verification Properties (model checking)

* Signals-Perspectives Conformance
* Internal Reactive Requirements (`t1...t6`)
* Invariants (`Inv1...Inv13`)
* Temporal Properties (`Prop1...Prop7`)