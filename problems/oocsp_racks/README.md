# OOCSP Rack Configuration

## Problem Description

This model tackles a **rack configuration problem**: given a set of hardware racks, frames, modules, and functional elements, find all valid ways to assemble them according to a fixed set of structural rules. The goal is _constraint satisfaction_ — there is no objective to minimise or maximise; the solver simply enumerates (or finds) valid configurations.

The model is also a demonstration of **OOCSP** (Object-Oriented Constraint Satisfaction Problem), a technique for systematically translating an object-oriented class diagram (with classes, inheritance, attributes, and associations) into a flat CSP that MiniZinc can solve. The encoding was developed by Gottfried Schenner and Richard Taupe at Siemens AG Österreich and submitted to the MiniZinc Challenge 2016.

## Background

Rack configuration is a classical product-configuration problem that appears in industrial automation and telecommunications, where physical units (racks) must be populated with functional modules according to strict compatibility and capacity rules. The OOCSP approach encodes the entire class hierarchy as integer ranges, allowing the solver to reason about object identity and class membership without enumerating objects explicitly.

---

## Object-Oriented Model

The configuration world contains the following classes (arranged in a hierarchy):

| Class                   | Description                                                                                                                    |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `Configuration`         | The top-level container. Exactly one instance exists per solution. Carries a `configtype` attribute (an integer, 1–100).       |
| `Rack`                  | An abstract rack type. Every rack belongs to exactly one `Configuration`.                                                      |
| `RackSingle`            | A concrete rack with exactly **4 frames**.                                                                                     |
| `RackDouble`            | A concrete rack with exactly **8 frames**.                                                                                     |
| `Frame`                 | A physical slot carrier. Each frame belongs to exactly one rack and can hold up to **6 modules**.                              |
| `Module`                | An abstract module type. Every module sits in exactly one frame and may be assigned to at most one element.                    |
| `ModuleI` – `ModuleV`   | Five concrete module types with different compatibility rules (see constraints below).                                         |
| `Element`               | An abstract functional element. Each element belongs to exactly one `Configuration` and is implemented by one or more modules. |
| `ElementA` – `ElementD` | Four concrete element types, each requiring a specific number and type of modules.                                             |

---

## Associations

| Association               | Meaning                                                     |
| ------------------------- | ----------------------------------------------------------- |
| `Element → Configuration` | Every element is part of exactly one configuration.         |
| `Rack → Configuration`    | Every rack is part of exactly one configuration.            |
| `Frame → Rack`            | Every frame belongs to exactly one rack.                    |
| `Module → Frame`          | Every module is installed in exactly one frame.             |
| `Module → Element`        | A module may be assigned to at most one element (optional). |

---

## Key Decision Variables

| Variable                      | Meaning                                                                                                        |
| ----------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `nrofobjects[c]`              | Number of instances of class `c` in the solution.                                                              |
| `start[c]`                    | The first object ID assigned to instances of class `c` (objects are identified by consecutive integer ranges). |
| `Configuration_configtype[o]` | The integer type attribute of configuration object `o`.                                                        |
| `Element_configuration[o]`    | Which configuration object element `o` belongs to.                                                             |
| `Rack_configuration[o]`       | Which configuration object rack `o` belongs to.                                                                |
| `Frame_rack[o]`               | Which rack frame `o` belongs to.                                                                               |
| `Module_frame[o]`             | Which frame module `o` is installed in.                                                                        |
| `Module_element[o]`           | Which element module `o` implements (0 if none).                                                               |

---

## Constraints

1. **Rack capacity**: A `RackSingle` holds exactly 4 frames; a `RackDouble` holds exactly 8 frames.
2. **Frame capacity**: A frame holds at most 6 modules.
3. **Element–module compatibility**:
   - `ElementA` requires exactly **1 ModuleI**.
   - `ElementB` requires exactly **2 ModuleII**.
   - `ElementC` requires exactly **3 ModuleIII**.
   - `ElementD` requires exactly **4 ModuleIV**.
4. **ModuleV**: Has no associated element and serves as a "filler" module.
5. **ModuleII co-location rule**: Whenever a `ModuleII` is present in a frame, that same frame must also contain at least one `ModuleV`.
6. **Same-frame rule**: All modules belonging to the same element must be installed in the same frame.
7. **Singleton configuration**: There is exactly one `Configuration` object per solution.
8. **Optional cardinality propagation**: The parameter `USECARDINALITYCONSTRAINTS` (boolean) enables a large set of linear arithmetic constraints derived automatically from the class diagram. These act as redundant constraints to help the solver prune the search space more aggressively.

---

## Parameters

The instance data file must supply bounds on how many objects of each class may appear, along with a maximum total object count:

| Parameter                               | Meaning                                                           |
| --------------------------------------- | ----------------------------------------------------------------- |
| `MAXNROFOBJECTS`                        | Upper bound on the total number of objects across all classes.    |
| `CLASS_<Name>_MIN` / `CLASS_<Name>_MAX` | Lower / upper bound on the number of instances of each class.     |
| `USECARDINALITYCONSTRAINTS`             | Whether to activate the redundant linear cardinality constraints. |

---

## Objective

**Satisfaction only** — the model seeks any valid assignment of objects and associations. There is no cost or quality objective to optimise.

---

## Notes & Uncertainties

- The OOCSP encoding technique is described in the context of the MiniZinc Challenge 2016. A broader description of the OOCSP approach can likely be found in work by Schenner and Taupe from Siemens AG Österreich, though a specific published paper has not been confirmed.
- The `leafclass_min` / `leafclass_max` arrays encode the class hierarchy using a depth-first traversal order. This is an internal encoding detail; adding new subclasses would require updating these arrays.
- The meaning of the `Configuration.configtype` attribute (values 1–100) is not specified in the model; it may be an application-specific type identifier whose semantics are defined externally.

---

## References

- Schenner, G. & Taupe, R. (2016). _OOCSP rack configuration example for MiniZinc Challenge 2016_. Siemens AG Österreich. (Model source comments.)
- [MiniZinc Challenge 2016](https://www.minizinc.org/challenge2016/results2016.html)

## Model update summary

Added concise inline comments in oocsp_racks.mzn to clarify:

- object/class association variable roles,
- satisfaction-only solve interpretation,
- search intent for valid rack configuration instances.
