/***********************************************************************/
/*                                                                     */
/*                           Coq Compiler                              */
/*                                                                     */
/*        Benjamin Gregoire, projets Logical and Cristal               */
/*                        INRIA Rocquencourt                           */
/*                                                                     */
/*                                                                     */
/***********************************************************************/

#ifndef _COQ_VALUES_
#define _COQ_VALUES_

#include <caml/alloc.h>
#include <caml/mlvalues.h>

#include <float.h>

#define Default_tag 0
#define Accu_tag 0

#define ATOM_ID_TAG 0
#define ATOM_INDUCTIVE_TAG 1
#define ATOM_TYPE_TAG 2
#define ATOM_PROJ_TAG 3
#define ATOM_FIX_TAG 4
#define ATOM_SWITCH_TAG 5
#define ATOM_COFIX_TAG 6
#define ATOM_COFIXEVALUATED_TAG 7

/* Les blocs accumulate */
#define Is_accu(v) (Is_block(v) && (Tag_val(v) == Accu_tag))
#define IS_EVALUATED_COFIX(v) (Is_accu(v) && Is_block(Field(v,1)) && (Tag_val(Field(v,1)) == ATOM_COFIXEVALUATED_TAG))
#define Is_double(v) (Tag_val(v) == Double_tag)

/* coq values for primitive operations */
#define coq_tag_C1 2
#define coq_tag_C0 1
#define coq_tag_pair 1
#define coq_true Val_int(0)
#define coq_false Val_int(1)
#define coq_Eq Val_int(0)
#define coq_Lt Val_int(1)
#define coq_Gt Val_int(2)
#define coq_FEq Val_int(0)
#define coq_FLt Val_int(1)
#define coq_FGt Val_int(2)
#define coq_FNotComparable Val_int(3)

#define coq_copy_double(val) caml_copy_double(val)
#define FLOAT_EXP_SHIFT (2101) /* 2*emax + prec */

#endif /* _COQ_VALUES_ */
