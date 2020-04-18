import group_theory.subgroup data.equiv.basic data.fin group_theory.perm.sign
import group_theory.presented_group group_theory.order_of_element
import group_theory.free_abelian_group
import algebra.group.hom algebra.group_power
import group_theory.group_action
import group_theory.representation.basic

#print group_representation 

inductive generator : Type
| x | y

variables a b : generator

def zgroup := free_group generator

def gx := free_group.of generator.x
