#include <list>
#include <string.h>

#define logvar(x) \
cout << __FILE__ << ":" << __LINE__ << " " << #x << " = " << x << endl;
#define logp \
cout << __FILE__ << ":" << __LINE__ << endl;
#define log(x) \
cout << __FILE__ << ":" << __LINE__ << " " << x << endl;

#include "prolog.hpp"

using namespace Prolog_impl;

// Global Data-------------------------------------------------------------

Init*  Prolog_impl::engine_queue = 0;
Init*  Prolog_impl::frame_queue = 0;
Engine Prolog_impl::the_engine;


// Global functions--------------------------------------------------------

// part of SWI-Prolog, but not exportet by header file
// /usr/local/src/swiprolog-4.0.9/src/pl-funcs.h
extern "C"
unsigned long pl_atom_to_term(term_t in_atom,
                              term_t out_term,
                              term_t out_bindings);

bool Prolog_impl::atom_to_term(const char* text, Term* t, list<Term::Binding>* b)
{
  Term in_atom = Atom(text);
  Term out_term;
  Term out_bindings;

  if (!pl_atom_to_term(in_atom.lsi, out_term.lsi, out_bindings.lsi))
    return false;

  if (t) *t = out_term;
  if (b) *b = out_bindings;
  return true;
}

extern "C"
unsigned long pl_copy_term(term_t in, term_t out);

Term Prolog_impl::copy_term(Term t)
{
  term_t t2 = PL_new_term_ref();
  if (!pl_copy_term(t.lsi, t2))
    throw LogicError("copy_term(Term)", "failure calling pl_copy_term()");
  return Term(t2);
}


void Prolog_impl::prolog_init(int argc, char const * const * argv)
{
  the_engine.init(argc, argv, "prolog_init()");
  engine_queue->thaw_all();
}

void Prolog_impl::prolog_halt(void)
{
  engine_queue->freeze_all();
  the_engine.halt();
}

void Prolog_impl::itoa(int n, char *str, int b)
{
  static char ziff[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
  char *str1;
  char a;

  if (n < 0)
    {
      n *= -1;
      *str++ = '-';
    }
  str1 = str;

  do
    {
      *str1++ = ziff[n % b];
      n /= b;
    }
  while (n);

  *str1-- = 0;

  while (str < str1)
    {
      a = *str1;
      *str1 = *str;
      *str = a;
      str++;
      str1--;
    }
}

string Prolog_impl::itoa(int x, int b=10)
{
  char P[40];
  itoa(x, P, b);
  return P;
}


// Class Engine------------------------------------------------------------

Query* Prolog_impl::Engine::active_query = 0;

void Prolog_impl::Engine::init(int argc, char const * const * argv, const char* place)
{
  halt();
  if ( !PL_initialise(argc, const_cast<char**>(argv)) )
    throw GeneralError(place, "failed to initialise the Prolog engine");

  Module::user_module = Module("user");

  status = running;
}

void Prolog_impl::Engine::halt(void)
{
  if (status == halted) return;
  PL_cleanup(0);
  status = halted;
}

Prolog_impl::Engine::Engine()
{
  status = halted;
}

Prolog_impl::Engine::~Engine()
{
  halt();
}


// Class StaticFunctor-----------------------------------------------------

Prolog_impl::StaticFunctor::~StaticFunctor()
{
  //delete init_name;
}

void Prolog_impl::StaticFunctor::thaw(void)
{
  /*log("StaticFunctor::thaw()");
  logvar(init_name);
  logvar(init_arity);*/
  handle = PL_new_functor(Atom(init_name).handle, init_arity);
}

void Prolog_impl::StaticFunctor::freeze(void)
{
  log("StaticFunctor::freeze(void)");
  handle = (functor_t) -1;
}


// Class StaticPredicate---------------------------------------------------

Prolog_impl::StaticPredicate::~StaticPredicate()
{
  //delete init_name;
  //delete init_module;
}

void Prolog_impl::StaticPredicate::thaw(void) {
  handle = PL_predicate(init_name, init_arity, init_module);
}

void Prolog_impl::StaticPredicate::freeze(void) {
  handle = (predicate_t) -1;
}


// Class StaticAtom--------------------------------------------------------

Prolog_impl::StaticAtom::~StaticAtom()
{
  //delete init_text;
}

void Prolog_impl::StaticAtom::thaw(void) {
  handle = PL_new_atom(init_text);
}

void Prolog_impl::StaticAtom::freeze(void) {
  handle = (atom_t) -1;
}


// Class Term--------------------------------------------------------------

Prolog_impl::Term::operator Term::Binding (void) const
{
  static StaticFunctor equals_functor("=", 2);
  const Term& me = *this;
  if (functor() != equals_functor
      || me[0].type() != tt_atom)
    throw ConversionError("Term::operator Term::Binding ()", "not a binding");
  return Term::Binding(me[0].to_string(), me[1]);
}

template <>
Term::operator list<char*>() const
{
  list<char*> l;
  term_t head = PL_new_term_ref();
  term_t tail = PL_copy_term_ref(lsi);
  while (!PL_get_nil(tail)) {
    if (!PL_get_list(tail, head, tail))
      throw ConversionError("Term::operator list<char*>()", "not a list");
    l.push_back(Term(head).to_str(default_cvt_flags|BUF_MALLOC));
  }
  return l;
}


// Class RecordedTerm------------------------------------------------------

Prolog_impl::RecordedTerm::~RecordedTerm()
{
  if (rec != (record_t) -1)
    PL_erase(rec);
}


// invalidate when the engine goes down
void RecordedTerm::freeze(void)
{
  rec = (record_t) -1;
}

void RecordedTerm::thaw(void)
{
  log("RecordedTerm::thaw()");
}

void RecordedTerm::duplicate(const RecordedTerm& rt)
{
  if (rec != (record_t) -1)
    PL_erase(rec);
  term_t tmp = PL_new_term_ref();
  PL_recorded(rt.rec, tmp);
  rec = PL_record(tmp);
}

void RecordedTerm::swap(RecordedTerm& rt)
{
  record_t tmp = rec;
  rec = rt.rec;
  rt.rec = tmp;
}


// Class StaticTerm--------------------------------------------------------

void StaticTerm::thaw()
{
  if (init_text)
    *this = Term(init_text);
}

void StaticTerm::freeze()
{
  rec = (record_t) -1;
}

void StaticTerm::swap(StaticTerm& st)
{
  RecordedTerm::swap(st);
  const char* tmp = init_text;
  init_text = st.init_text;
  st.init_text = tmp;
}

void StaticTerm::duplicate(const StaticTerm& st)
{
  RecordedTerm::duplicate(st);
  init_text = st.init_text;
}


// Class Frame-------------------------------------------------------------

Frame* Frame::last_frame = 0;


// Class Query-------------------------------------------------------------

// not called
void Prolog_impl::Query::thaw()
{
}

// called when the frame is left
void Prolog_impl::Query::freeze()
{
  predargs = (term_t) -1;
  close();
}


// Class StaticQuery-------------------------------------------------------


void Prolog_impl::StaticQuery::Init_Engine::thaw() 
{
  sq->engine_thaw();
}

void Prolog_impl::StaticQuery::Init_Engine::freeze() 
{
  sq->engine_freeze();
}


// called when the engine has been initialised
void Prolog_impl::StaticQuery::engine_thaw()
{
  ctx = Module(init_module);
  predargs = (term_t) -1;
  open = false;

  if (calltype == from_pred) {
    // make query from predicate
    pred = Predicate(init_pred, arity);
  } else {
    // make query from callterm
    Frame fr;
    Term t;
    list<Term::Binding> b;

    atom_to_term(init_text, &t, &b);
    pred = Predicate(t.functor(), ctx);
    arity = pred.arity();

    Term ct(Functor("args", arity + b.size()));
    int i;
    for (i = 0; i < arity; i++)
      ct[i].unify(t[i]);
    nargs = 0;
    for (list<Term::Binding>::iterator it = b.begin();
         it != b.end();
         ++it, i++) {
      ct[i].unify(it->var);
      nargs++;
    }

    callterm = ct;
  }
}

// called before the engine goes down
void Prolog_impl::StaticQuery::engine_freeze()
{
  predargs = (term_t) -1;
  close();
  // qid, ctx, pred, predargs, callterm invalidated
}


// Class Module------------------------------------------------------------

Module Prolog_impl::Module::user_module;



// Class ForeignPredicate--------------------------------------------------

void ForeignPredicate::thaw(void)
{
  PL_register_foreign(name, arity, wrapper, PL_FA_VARARGS);
}

void ForeignPredicate::freeze(void)
{
}


// Exceptions--------------------------------------------------------------

Term FormatError::as_term() const
{
  return make_term("error", Atom("format_error"),
                   make_term("context", Atom(place), Atom(msg)));
}

string FormatError::message() const
{
  return string(place) + ": " + msg;
}

Term LogicError::as_term() const
{
  return make_term("error", Atom("logic_error"), make_term("context", Atom(place), Atom(msg)));
}

string LogicError::message() const
{
  return string("Logic error in ") + place + ": " + msg;
}

Term ConversionError::as_term() const
{
  return make_term("error", Atom("conversion_error"),
                   make_term("context", Atom(place), Atom(msg)));
}

string ConversionError::message() const
{
  return string("Conversion error in ") + place + " :\n" + msg;
}

Term ParseError::as_term() const
{
  return make_term("error", Atom("parse_error"),
                   make_term("context", Atom(place), Atom(text)));
}

string ParseError::message() const
{
  return string("Parse error in ") + place + " in this text: " + text;
}

Term CvtError::as_term() const
{
  return make_term("error", Atom("cvt_error"),
                   make_term("context", Atom(place), Atom(msg)));
}

Term GeneralError::as_term() const
{
  return make_term("error", Atom("general_error"), make_term("context", Atom(place), Atom(msg)));
}

string GeneralError::message() const
{
  return string(place) + ": " + msg;
}

Term SafePrologException::as_term() const
{
  return Term::from_external(external);
}

string SafePrologException::message() const
{
  Frame frame;
  string msg = Term::from_external(external).to_string();
  frame.rewind();
  return msg;
}

Term UnsafePrologException::as_term() const
{
  return ex;
}

string UnsafePrologException::message() const
{
  return ex.to_string();
}
