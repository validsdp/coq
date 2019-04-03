#ifndef _COQ_FLOAT64_
#define _COQ_FLOAT64_

#include <math.h>

double coq_fmul(double x, double y)
{
  return x * y;
}

value coq_fmul_byte(value x, value y)
{
  return caml_copy_double(coq_fmul(Double_val(x), Double_val(y)));
}

double coq_fadd(double x, double y)
{
  return x + y;
}

value coq_fadd_byte(value x, value y)
{
  return caml_copy_double(coq_fadd(Double_val(x), Double_val(y)));
}

double coq_fsub(double x, double y)
{
  return x - y;
}

value coq_fsub_byte(value x, value y)
{
  return caml_copy_double(coq_fsub(Double_val(x), Double_val(y)));
}

double coq_fdiv(double x, double y)
{
  return x / y;
}

value coq_fdiv_byte(value x, value y)
{
  return caml_copy_double(coq_fdiv(Double_val(x), Double_val(y)));
}

double coq_fsqrt(double x)
{
  return sqrt(x);
}

value coq_fsqrt_byte(value x)
{
  return caml_copy_double(coq_fsqrt(Double_val(x)));
}

double coq_next_up(double x)
{
  return nextafter(x, INFINITY);
}

value coq_next_up_byte(value x)
{
  return caml_copy_double(coq_next_up(Double_val(x)));
}

double coq_next_down(double x)
{
  return nextafter(x, -INFINITY);
}

value coq_next_down_byte(value x)
{
  return caml_copy_double(coq_next_down(Double_val(x)));
}

#endif /* _COQ_FLOAT64_ */
