/**************************************************************************************[minisat.cc]
Copyright (c) 2008-2010, Niklas Sorensson
              2008, Koen Claessen

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdlib.h>

#ifdef USE_GLUCOSE
#include "glucose-syrup-4.1/simp/SimpSolver.h"
using namespace Glucose;
#else
#include "minisat/simp/SimpSolver.h"
using namespace Minisat;
#endif


struct minisat_solver_t : public SimpSolver { 
    vec<Lit> clause;
    vec<Lit> assumps;
};

extern "C" {

#include "minisat.h"

// This implementation of lbool may or not may be an exact mirror of the C++ implementation:
//
extern const minisat_lbool minisat_l_True  = 1;
extern const minisat_lbool minisat_l_False = 0;
extern const minisat_lbool minisat_l_Undef = -1;

static inline minisat_lbool toC(lbool a)
{
    return a == l_True  ? minisat_l_True
         : a == l_False ? minisat_l_False
         : minisat_l_Undef;
}

static inline lbool fromC(minisat_lbool a)
{
    return a == minisat_l_True  ? l_True
         : a == minisat_l_False ? l_False
         : l_Undef;
}


// TODO: why are these here?
minisat_lbool minisat_get_l_True     (void){ return minisat_l_True; }
minisat_lbool minisat_get_l_False    (void){ return minisat_l_False; }
minisat_lbool minisat_get_l_Undef    (void){ return minisat_l_Undef; }

// Solver C-API wrapper functions:
//
minisat_solver* minisat_new             (void){ return new minisat_solver_t(); }
void          minisat_delete          (minisat_solver *s){ delete s; }
minisat_Var   minisat_newVar          (minisat_solver *s){ return s->newVar(); }
minisat_Lit   minisat_newLit          (minisat_solver *s){ return toInt(mkLit(s->newVar())); }
minisat_Lit   minisat_mkLit           (minisat_Var x){ return toInt(mkLit(x)); }
minisat_Lit   minisat_mkLit_args      (minisat_Var x, int sign){ return toInt(mkLit(x,sign)); }
minisat_Lit   minisat_negate          (minisat_Lit p){ return toInt(~toLit(p)); }
minisat_Var   minisat_var             (minisat_Lit p){ return var(toLit(p)); }
int          minisat_sign            (minisat_Lit p){ return sign(toLit(p)); }
void         minisat_addClause_begin (minisat_solver *s){ s->clause.clear(); }
void         minisat_addClause_addLit(minisat_solver *s, minisat_Lit p){ s->clause.push(toLit(p)); }
int          minisat_addClause_commit(minisat_solver *s){ return s->addClause_(s->clause); }
int          minisat_simplify        (minisat_solver *s){ return s->simplify(); }

// NOTE: Currently these run with default settings for implicitly calling preprocessing. Turn off
// before if you don't need it. This may change in the future.
void         minisat_solve_begin     (minisat_solver *s){ s->assumps.clear(); }
void         minisat_solve_addLit    (minisat_solver *s, minisat_Lit p){ s->assumps.push(toLit(p)); }
int          minisat_solve_commit    (minisat_solver *s){ return s->solve(s->assumps); }
minisat_lbool minisat_limited_solve_commit (minisat_solver *s){ return toC(s->solveLimited(s->assumps)); }

int          minisat_okay            (minisat_solver *s){ return s->okay(); }

#ifdef USE_GLUCOSE
#else
void         minisat_setPolarity     (minisat_solver *s, minisat_Var v, minisat_lbool lb){ s->setPolarity(v, fromC(lb)); }
#endif

void         minisat_setDecisionVar  (minisat_solver *s, minisat_Var v, int b){ s->setDecisionVar(v, b); }
minisat_lbool minisat_value_Var      (minisat_solver *s, minisat_Var x){ return toC(s->value(x)); }
minisat_lbool minisat_value_Lit      (minisat_solver *s, minisat_Lit p){ return toC(s->value(toLit(p))); }
minisat_lbool minisat_modelValue_Var (minisat_solver *s, minisat_Var x){ return toC(s->modelValue(x)); }
minisat_lbool minisat_modelValue_Lit (minisat_solver *s, minisat_Lit p){ return toC(s->modelValue(toLit(p))); }
int          minisat_num_assigns     (minisat_solver *s){ return s->nAssigns(); }
int          minisat_num_clauses     (minisat_solver *s){ return s->nClauses(); }
int          minisat_num_learnts     (minisat_solver *s){ return s->nLearnts(); }
int          minisat_num_vars        (minisat_solver *s){ return s->nVars(); }
int          minisat_num_freeVars    (minisat_solver *s){ return s->nFreeVars(); }
int          minisat_conflict_len    (minisat_solver *s){ return s->conflict.size(); }
minisat_Lit  minisat_conflict_nthLit (minisat_solver *s, int i){ return toInt(s->conflict[i]); }
void         minisat_set_verbosity   (minisat_solver *s, int v){ s->verbosity = v; }
int          minisat_get_verbosity   (minisat_solver *s){ return s->verbosity; }
int          minisat_num_conflicts   (minisat_solver *s){ return s->conflicts; }
int          minisat_num_decisions   (minisat_solver *s){ return s->decisions; }
int          minisat_num_restarts    (minisat_solver *s){ return s->starts; }
int          minisat_num_propagations(minisat_solver *s){ return s->propagations; }
void         minisat_set_conf_budget (minisat_solver* s, int x){ s->setConfBudget(x); }
void         minisat_set_prop_budget (minisat_solver* s, int x){ s->setPropBudget(x); }
void         minisat_no_budget       (minisat_solver* s){ s->budgetOff(); }

// Resource constraints:
void minisat_interrupt(minisat_solver* s) {s->interrupt (); }
void minisat_clearInterrupt(minisat_solver* s) {s->clearInterrupt (); }

// SimpSolver methods:
void         minisat_setFrozen       (minisat_solver* s, minisat_Var v, minisat_bool b) { s->setFrozen(v, b); }
minisat_bool minisat_isEliminated    (minisat_solver* s, minisat_Var v) { return s->isEliminated(v); }
minisat_bool minisat_eliminate       (minisat_solver* s, minisat_bool turn_off_elim){ return s->eliminate(turn_off_elim); }

// Convenience functions for actual c-programmers (not language interfacing people):
//
int  minisat_solve(minisat_solver *s, int len, minisat_Lit *ps)
{
    s->assumps.clear();
    for (int i = 0; i < len; i++)
        s->assumps.push(toLit(ps[i]));
    return s->solve(s->assumps);
}


minisat_lbool minisat_limited_solve(minisat_solver *s, int len, minisat_Lit *ps)
{
    s->assumps.clear();
    for (int i = 0; i < len; i++)
        s->assumps.push(toLit(ps[i]));
    return toC(s->solveLimited(s->assumps));
}


int  minisat_addClause(minisat_solver *s, int len, minisat_Lit *ps)
{
    s->clause.clear();
    for (int i = 0; i < len; i++)
        s->clause.push(toLit(ps[i]));
    return s->addClause_(s->clause);
}


}
