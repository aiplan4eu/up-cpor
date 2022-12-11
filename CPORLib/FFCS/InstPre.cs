using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

using static CPORLib.FFCS.Connective;
using static CPORLib.FFCS.Inertia;
using static CPORLib.FFCS.DomainProperties;
using static CPORLib.FFCS.Output;
using static CPORLib.FFCS.Planning;
using static CPORLib.FFCS.FFUtilities;

namespace CPORLib.FFCS
{
    public  class InstPre
    {

        /*********************************************************************
         * File: inst_pre.c
         * Description: functions for instantiating operators, preprocessing part.
         *              - transform domain into integers
         *              - inertia preprocessing:
         *                  - collect inertia info
         *                  - split initial state in special arrays
         *              - Wff normalization:
         *                  - simplification
         *                  - quantifier expansion
         *                  - NOT s down
         *              - negative preconditions translation
         *              - split operators into easy and hard to instantiate
         *
         *              - full DNF functions, only feasible for fully instantiated 
         *                formulae
         *
         * Author: Joerg Hoffmann 2000
         *
         *********************************************************************/


        /*******************************************************
         * TRANSFORM DOMAIN INTO INTEGER (FACT) REPRESENTATION *
         *******************************************************/


        public  string[] lvar_names = new string[Constants.MAX_VARS];
        public  int[] lvar_types = new int[Constants.MAX_VARS];


        public  void encode_domain_in_integers()

        {

            int i, j;
            Effect ief;
            Literal ilit;

            collect_all_strings();

            create_integer_representation();

            if (gcmd_line.display_info == 104)
            {
                FFUtilities.Write("\n\nfirst step initial state is:");
                for (i = 0; i < FF.DP.gnum_full_initial; i++)
                {
                    FFUtilities.Write("\n");
                    Output.print_Fact(FF.DP.gfull_initial[i]);
                }

                FFUtilities.Write("\n\nfirst step operators are:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    Output.print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");

                FFUtilities.Write("\n\nfirst step goal is:\n");
                Output.print_Wff(FF.DP.ggoal, 0);
            }

            /* treat derived predicates info
             */
            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (!FF.DP.goperators[i].axiom) continue;
                FF.DP.gderived[FF.DP.goperators[i].effects.effects.fact.predicate] = true;
            }
            /* syntax check: no derived predicates in effects of normal ops!
             */
            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (FF.DP.goperators[i].axiom) continue;
                for (ief = FF.DP.goperators[i].effects; ief != null; ief = ief.next)
                {
                    for (ilit = ief.effects; ilit != null; ilit = ilit.next)
                    {
                        if (FF.DP.gderived[ilit.fact.predicate])
                        {
                            FFUtilities.Write("\n\noperators are not allowed to affect derived predicates! check input files!\n\n");
                            Exit(1);
                        }
                    }
                }
            }

            if (gcmd_line.display_info == 103)
            {
                FFUtilities.Write("\nconstant table:");
                for (i = 0; i < FF.DP.gnum_constants; i++)
                {
                    FFUtilities.Write("\n%d -. %s", i, FF.DP.gconstants[i]);
                }

                FFUtilities.Write("\n\ntypes table:");
                for (i = 0; i < FF.DP.gnum_types; i++)
                {
                    FFUtilities.Write("\n%d -. %s: ", i, FF.DP.gtype_names[i]);
                    for (j = 0; j < FF.DP.gtype_size[i]; j++)
                    {
                        FFUtilities.Write("%d ", FF.DP.gtype_consts[i,j]);
                    }
                }

                FFUtilities.Write("\n\npredicates table:");
                for (i = 0; i < FF.DP.gnum_predicates; i++)
                {
                    FFUtilities.Write("\n%3d -. %s: ", i, FF.DP.gpredicates[i]);
                    for (j = 0; j < FF.DP.garity[i]; j++)
                    {
                        FFUtilities.Write("%s ", FF.DP.gtype_names[FF.DP.gpredicates_args_type[i,j]]);
                    }
                    FFUtilities.Write(" DERIVED? %d", FF.DP.gderived[i]);
                }
                FFUtilities.Write("\n\n");
            }

        }



        public  void collect_all_strings()

        {

            FactList f;
            TokenList t;
            int p_num, type_num, c_num, ar;
            int i;

            /* first are types and their objects. for = we make sure that there
             * is one type that contains all objects.
             */
            //Main.DP.gtype_names[0] = new_Token(50);
            FF.DP.gtype_names[0] = "ARTFICIAL-ALL-OBJECTS";
            FF.DP.gtype_size[0] = 0;
            for (i = 0; i < Constants.MAX_CONSTANTS; i++)
            {
                FF.DP.gis_member[i,0] = false;
            }
            FF.DP.gnum_types = 1;

            for (f = FF.DP.gorig_constant_list; f != null; f = f.next)
            {
                if ((type_num = position_in_types_table(f.item.next.item)) == -1)
                {
                    if (FF.DP.gnum_types == Constants.MAX_TYPES)
                    {
                        FFUtilities.Write("\ntoo many types! increase Constants.MAX_TYPES (currently %d)\n\n",
                               Constants.MAX_TYPES);
                        Exit(1);
                    }
                    //Main.DP.gtype_names[Main.DP.gnum_types] = new_Token(strlen(f.item.next.item) + 1);
                    FF.DP.gtype_names[FF.DP.gnum_types] = f.item.next.item;
                    FF.DP.gtype_size[FF.DP.gnum_types] = 0;
                    for (i = 0; i < Constants.MAX_CONSTANTS; i++)
                    {
                        FF.DP.gis_member[i,FF.DP.gnum_types] = false;
                    }
                    type_num = FF.DP.gnum_types++;
                }

                if ((c_num = position_in_constants_table(f.item.item)) == -1)
                {
                    if (FF.DP.gnum_constants == Constants.MAX_CONSTANTS)
                    {
                        FFUtilities.Write("\ntoo many constants! increase Constants.MAX_CONSTANTS (currently %d)\n\n",
                               Constants.MAX_CONSTANTS);
                        Exit(1);
                    }
                    //Main.DP.gconstants[Main.DP.gnum_constants] = new_Token(strlen(f.item.item) + 1);
                    FF.DP.gconstants[FF.DP.gnum_constants] = f.item.item;
                    c_num = FF.DP.gnum_constants++;

                    /* all constants into 0-type.
                     */
                    if (FF.DP.gtype_size[0] == Constants.MAX_TYPE)
                    {
                        FFUtilities.Write("\ntoo many consts in type %s! increase Constants.MAX_TYPE (currently %d)\n\n",
                               FF.DP.gtype_names[0], Constants.MAX_TYPE);
                        Exit(1);
                    }
                    FF.DP.gtype_consts[0,FF.DP.gtype_size[0]++] = c_num;
                    FF.DP.gis_member[c_num,0] = true;
                }

                if (!FF.DP.gis_member[c_num,type_num])
                {
                    if (FF.DP.gtype_size[type_num] == Constants.MAX_TYPE)
                    {
                        FFUtilities.Write("\ntoo many consts in type %s! increase Constants.MAX_TYPE (currently %d)\n\n",
                               FF.DP.gtype_names[type_num], Constants.MAX_TYPE);
                        Exit(1);
                    }
                    FF.DP.gtype_consts[type_num,FF.DP.gtype_size[type_num]++] = c_num;
                    FF.DP.gis_member[c_num,type_num] = true;
                }
            }

            /* next are predicates; first of all, create in-built predicate =
             */
            //Main.DP.gpredicates[0] = new_Token(5);
            FF.DP.gpredicates[0] = "=";
            FF.DP.gpredicates_args_type[0,0] = 0;/* all objects type */
            FF.DP.gpredicates_args_type[0,1] = 0;
            FF.DP.garity[0] = 2;
            FF.DP.gnum_predicates = 1;

            for (f = FF.DP.gpredicates_and_types; f != null; f = f.next)
            {
                if ((p_num = position_in_predicates_table(f.item.item)) != -1)
                {
                    FFUtilities.Write("\npredicate %s declared twice!\n\n", f.item.item);
                    Exit(1);
                }
                if (FF.DP.gnum_predicates == Constants.MAX_PREDICATES)
                {
                    FFUtilities.Write("\ntoo many predicates! increase Constants.MAX_PREDICATES (currently %d)\n\n",
                       Constants.MAX_PREDICATES);
                    Exit(1);
                }
                //Main.DP.gpredicates[Main.DP.gnum_predicates] = new_Token(strlen(f.item.item) + 1);
                FF.DP.gpredicates[FF.DP.gnum_predicates]= f.item.item;
                ar = 0;
                for (t = f.item.next; t != null; t = t.next)
                {
                    if ((type_num = position_in_types_table(t.item)) == -1)
                    {
                        FFUtilities.Write("\npredicate %s is declared to use unknown or empty type %s\n\n",
                               f.item.item, t.item);
                        Exit(1);
                    }
                    if (ar == Constants.MAX_ARITY)
                    {
                        FFUtilities.Write("\narity of %s to hiFF.Search.gH! increase Constants.MAX_ARITY (currently %d)\n\n",
                               FF.DP.gpredicates[FF.DP.gnum_predicates], Constants.MAX_ARITY);
                        Exit(1);
                    }
                    FF.DP.gpredicates_args_type[FF.DP.gnum_predicates,ar++] = type_num;
                }
                FF.DP.garity[FF.DP.gnum_predicates] = ar;
                FF.DP.gderived[FF.DP.gnum_predicates++] = false;
            }

            ////free_FactList(Main.DP.gorig_constant_list);
            ////free_FactList(Main.DP.Main.DP.gpredicates_and_types);

        }



        public int position_in_types_table(string str)

        {

            int i;

            /* start at 1 because 0 is our artificial one
             */
            for (i = 1; i < FF.DP.gnum_types; i++)
            {
                if (str == FF.DP.gtype_names[i] ||
                 (str == FF.DP.gtype_names[i]))
                {
                    break;
                }
            }

            return (i == FF.DP.gnum_types) ? -1 : i;

        }



        public  int position_in_constants_table(string str)

        {

            int i;

            for (i = 0; i < FF.DP.gnum_constants; i++)
            {
                if (str == FF.DP.gconstants[i] ||
                 (str == FF.DP.gconstants[i]))
                {
                    break;
                }
            }

            return (i == FF.DP.gnum_constants) ? -1 : i;

        }



        public  int position_in_predicates_table(string str)

        {

            int i;

            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                if (str == FF.DP.gpredicates[i] ||
                 (str == FF.DP.gpredicates[i]))
                {
                    break;
                }
            }

            return (i == FF.DP.gnum_predicates) ? -1 : i;

        }



        public  void create_integer_representation()

        {

            PlNode n, nn;
            PlOperator o;
            Operator tmp;
            FactList ff;
            int type_num, i, s = 0;

            if (FF.Parsing.gorig_initial_facts != null)
            {
                for (n = FF.Parsing.gorig_initial_facts.sons; n != null; n = n.next) s++;
                s += FF.DP.gnum_constants;/* space for equalities */
                FF.DP.gfull_initial = new Fact[s];// (Fact)calloc(s, sizeof(Fact));
                for (n = FF.Parsing.gorig_initial_facts.sons; n != null; n = n.next)
                {
                    FF.DP.gfull_initial[FF.DP.gnum_full_initial] = make_Fact(n, 0);

                    //print_Fact(Main.DP.gfull_initial[Main.DP.gnum_full_initial]);

                    if (FF.DP.gfull_initial[FF.DP.gnum_full_initial].predicate == -1)
                    {
                        FFUtilities.Write("\nequality in initial state! check input files.\n\n");
                        Exit(1);
                    }
                    FF.DP.gnum_full_initial++;
                }
                //free_PlNode(FF.Parsing.gorig_initial_facts);
            }
            /* now insert all our artificial equality constraints into initial state.
             */
            for (i = 0; i < FF.DP.gnum_constants; i++)
            {
                FF.DP.gfull_initial[FF.DP.gnum_full_initial] = new Fact();
                FF.DP.gfull_initial[FF.DP.gnum_full_initial].predicate = 0;
                FF.DP.gfull_initial[FF.DP.gnum_full_initial].args[0] = i;
                FF.DP.gfull_initial[FF.DP.gnum_full_initial].args[1] = i;
                FF.DP.gnum_full_initial++;
            }
            /* FINITO. the rest of equality handling will fully
             * automatically be done by the rest of the machinery.
             */

            FF.DP.ggoal = make_Wff(FF.Parsing.gorig_goal_facts, 0);

            for (o = FF.Parsing.gloaded_ops; o != null; o = o.next)
            {
                tmp = new Operator(o.name, o.number_of_real_params);
                tmp.axiom = o.axiom;
                if (tmp.axiom)
                {
                    tmp.stratum = 0;
                }
                else
                {
                    tmp.stratum = -1;
                }

                for (ff = o.parameters; ff != null; ff = ff.next)
                {
                    if ((type_num = position_in_types_table(ff.item.next.item)) == -1)
                    {
                        FFUtilities.Write("\nwarning: parameter %s of op %s has unknown or empty type %s. skipping op",
                               ff.item.item, o.name, ff.item.next.item);
                        break;
                    }
                    if (tmp.num_vars == Constants.MAX_VARS)
                    {
                        FFUtilities.Write("\ntoo many parameters! increase Constants.MAX_VARS (currently %d)\n\n",
                               Constants.MAX_VARS);
                        Exit(1);
                    }
                    for (i = 0; i < tmp.num_vars; i++)
                    {
                        if (tmp.var_names[i] == ff.item.item ||
                             (tmp.var_names[i] == ff.item.item))
                        {
                            FFUtilities.Write("\nwarning: operator %s parameter %s overwrites previous declaration\n\n",
                               tmp.name, ff.item.item);
                        }
                    }
                    //tmp.var_names[tmp.num_vars] = new_Token(strlen(ff.item.item) + 1);
                    tmp.var_names[tmp.num_vars] = ff.item.item;
                    tmp.var_types[tmp.num_vars++] = type_num;
                }
                if (ff != null)
                {
                    //free_Operator(tmp);
                    continue;
                }

                for (i = 0; i < tmp.num_vars; i++)
                {
                    lvar_types[i] = tmp.var_types[i];
                    lvar_names[i] = tmp.var_names[i];
                }

                tmp.preconds = make_Wff(o.preconds, tmp.num_vars);

                if (o.effects != null)
                {
                    /* in make_effect, make sure that no one affects equality.
                     */
                    nn = o.effects.sons;
                    while (nn != null &&
                        (tmp.effects = make_effect(nn, tmp.num_vars)) == null)
                    {
                        nn = nn.next;
                    }
                    if (nn != null)
                    {
                        for (n = nn.next; n != null; n = n.next)
                        {
                            if ((tmp.effects.prev = make_effect(n, tmp.num_vars)) == null)
                            {
                                continue;
                            }
                            tmp.effects.prev.next = tmp.effects;
                            tmp.effects = tmp.effects.prev;
                        }
                    }
                }

                if (FF.DP.gnum_operators == Constants.MAX_OPERATORS)
                {
                    FFUtilities.Write("\ntoo many operators! increase Constants.MAX_OPERATORS (currently %d)\n\n",
                       Constants.MAX_OPERATORS);
                    Exit(1);
                }
                FF.DP.goperators[FF.DP.gnum_operators++] = tmp;
            }

            if (false)
            {
                /* currently not in use; leads to free memory reads and
                 * free memory frees (no memory leaks), which are hard to explain.
                 *
                 * almost no memory consumption anyway.
                 */
                //free_PlOperator(FF.Parsing.gloaded_ops);
            }

        }



        public  Fact make_Fact(PlNode n, int num_vars)

        {

            Fact f = new Fact();

          

            int m, i;
            TokenList t;

            if (n.atom == null)
            {
                /* can't happen after previous syntax check. Oh well, whatever...
                 */
                FFUtilities.Write("\nillegal (empty) atom used in domain. check input files\n\n");
                Exit(1);
            }

            //Utilities.Write("Fact: " + n.atom.item);

            f.predicate = position_in_predicates_table(n.atom.item);
            if (f.predicate == -1)
            {
                FFUtilities.Write("\nundeclared predicate " + n.atom.item + " used in domain definition\n\n");
                Exit(1);
            }

            m = 0;
            for (t = n.atom.next; t != null; t = t.next)
            {
                //Utilities.Write(" " + t.item);
                if (t.item[0] == '?')
                {
                    for (i = num_vars - 1; i > -1; i--)
                    {
                        /* downwards, to always get most recent declaration/quantification
                         * of that variable
                         */
                        if (lvar_names[i] == t.item ||
                             (lvar_names[i] == t.item))
                        {
                            break;
                        }
                    }
                    if (i == -1)
                    {
                        FFUtilities.Write("\nundeclared variable %s in literal %s. check input files\n\n",
                               t.item, n.atom.item);
                        Exit(1);
                    }
                    if (f.predicate != -1 &&
                     lvar_types[i] != FF.DP.gpredicates_args_type[f.predicate,m] &&
                     !is_subtype(lvar_types[i], FF.DP.gpredicates_args_type[f.predicate,m]))
                    {
                        FFUtilities.Write("\ntype of var %s does not match type of arg %d of predicate %s\n\n",
                               lvar_names[i], m, FF.DP.gpredicates[f.predicate]);
                        Exit(1);
                    }
                    f.args[m] = FFUtilities.ENCODE_VAR(i);
                }
                else
                {
                    if ((f.args[m] =
                      position_in_constants_table(t.item)) == -1)
                    {
                        FFUtilities.Write("\nunknown constant %s in literal %s. check input files\n\n",
                               t.item, n.atom.item);
                        Exit(1);
                    }
                    if (f.predicate != -1 &&
                     !FF.DP.gis_member[f.args[m],FF.DP.gpredicates_args_type[f.predicate,m]])
                    {
                        FFUtilities.Write("\ntype mismatch: constant %s as arg %d of %s. check input files\n\n",
                               FF.DP.gconstants[f.args[m]], m, FF.DP.gpredicates[f.predicate]);
                        Exit(1);
                    }
                }
                m++;
            }

            //Utilities.WriteLine();

            if (f.predicate == -1)
            {
                if (m != 2)
                {
                    FFUtilities.Write("\nfound eq - predicate with %d arguments. check input files\n\n",
                       m);
                    Exit(1);
                }
            }
            else
            {
                if (m != FF.DP.garity[f.predicate])
                {
                    FFUtilities.Write("\npredicate %s is declared to have %d (not %d) arguments. check input files\n\n",
                       FF.DP.gpredicates[f.predicate],
                       FF.DP.garity[f.predicate], m);
                    Exit(1);
                }
            }
            return f;
        }



        public  bool is_subtype(int t1, int t2)

        {

            int i;

            for (i = 0; i < FF.DP.gtype_size[t1]; i++)
            {
                if (!FF.DP.gis_member[FF.DP.gtype_consts[t1,i],t2])
                {
                    return false;
                }
            }

            return true;

        }



        public  WffNode make_Wff(PlNode p, int num_vars)

        {

            WffNode tmp;
            int i, t;
            PlNode n;

            if (p == null)
            {
                tmp = null;
                return tmp;
            }

            tmp = new WffNode(p.connective);
            switch (p.connective)
            {
                case Connective.ALL:
                case Connective.EX:
                    for (i = 0; i < num_vars; i++)
                    {
                        if (lvar_names[i] == p.atom.item ||
                         (lvar_names[i] == p.atom.item))
                        {
                            FFUtilities.Write("\nwarning: var quantification of %s overwrites previous declaration\n\n",
                                   p.atom.item);
                        }
                    }
                    if ((t = position_in_types_table(p.atom.next.item)) == -1)
                    {
                        FFUtilities.Write("\nwarning: quantified var %s has unknown or empty type %s. simplifying.\n\n",
                           p.atom.item, p.atom.next.item);
                        tmp.connective = (p.connective == Connective.EX) ? Connective.FAL : Connective.TRU;
                        break;
                    }
                    tmp.var = num_vars;
                    tmp.var_type = t;
                    //tmp.var_name = new_Token(strlen(p.atom.item) + 1);
                    tmp.var_name = p.atom.item;
                    lvar_names[num_vars] = p.atom.item;
                    lvar_types[num_vars] = t;
                    tmp.son = make_Wff(p.sons, num_vars + 1);
                    break;
                case Connective.AND:
                case Connective.OR:
                    if (p.sons == null)
                    {
                        FFUtilities.Write("\nwarning: empty con/disjunction in domain definition. simplifying.\n\n");
                        tmp.connective = (p.connective == Connective.OR) ? Connective.FAL : Connective.TRU;
                        break;
                    }
                    tmp.sons = make_Wff(p.sons, num_vars);
                    for (n = p.sons.next; n != null; n = n.next)
                    {
                        tmp.sons.prev = make_Wff(n, num_vars);
                        tmp.sons.prev.next = tmp.sons;
                        tmp.sons = tmp.sons.prev;
                    }
                    break;
                case Connective.NOT:
                    tmp.son = make_Wff(p.sons, num_vars);
                    break;
                case Connective.ATOM:
                    tmp.fact = new Fact();
                    tmp.fact = make_Fact( p, num_vars);
                    break;
                case Connective.TRU:
                case Connective.FAL:
                    break;
                default:
                    FFUtilities.Write("\nforbidden connective %d in Pl Wff. must be a bug somewhere...\n\n",
                       p.connective);
                    Exit(1);
                    break;
            }

            return tmp;

        }



        public  Effect make_effect(PlNode p, int num_vars)

        {

            Effect tmp = new Effect();
            PlNode n, m;
            int t, i;

            for (n = p; n != null && n.connective == Connective.ALL; n = n.sons)
            {
                if ((t = position_in_types_table(n.atom.next.item)) == -1)
                {
                    FFUtilities.Write("\nwarning: effect parameter %s has unknown or empty type %s. skipping effect.\n\n",
                       n.atom.item, n.atom.next.item);
                    return null;
                }
                for (i = 0; i < num_vars + tmp.num_vars; i++)
                {
                    if (lvar_names[i] == n.atom.item ||
                     (lvar_names[i] == n.atom.item))
                    {
                        FFUtilities.Write("\nwarning: effect parameter %s overwrites previous declaration\n\n",
                               n.atom.item);
                    }
                }
                lvar_types[num_vars + tmp.num_vars] = t;
                lvar_names[num_vars + tmp.num_vars] = n.atom.item;
                //tmp.var_names[tmp.num_vars] = new_Token(strlen(n.atom.item) + 1);
                tmp.var_names[tmp.num_vars] = n.atom.item;
                tmp.var_types[tmp.num_vars++] = t;
            }

            if (n == null || n.connective != Connective.WHEN)
            {
                FFUtilities.Write("\nnon WHEN %d at end of effect parameters. debug me\n\n",
                   n.connective);
                Exit(1);
            }

            tmp.conditions = make_Wff(n.sons, num_vars + tmp.num_vars);

            if (n.sons.next.connective != Connective.AND)
            {
                FFUtilities.Write("\nnon AND %d in front of literal effect list. debug me\n\n",
                   n.sons.next.connective);
                Exit(1);
            }
            if (n.sons.next.sons == null)
            {
                return tmp;
            }
            m = n.sons.next.sons;
            tmp.effects = new Literal();
            if (m.connective == NOT)
            {
                tmp.effects.negated = true;
                tmp.effects.fact = make_Fact(m.sons, num_vars + tmp.num_vars);
                if ((tmp.effects.fact).predicate == 0)
                {
                    FFUtilities.Write("\n\nequality in effect! check input files!\n\n");
                    Exit(1);
                }
            }
            else
            {
                tmp.effects.negated = false;
                tmp.effects.fact = make_Fact( m, num_vars + tmp.num_vars);
                if ((tmp.effects.fact).predicate == 0)
                {
                    FFUtilities.Write("\n\nequality in effect! check input files!\n\n");
                    Exit(1);
                }
            }
            for (m = m.next; m != null; m = m.next)
            {
                tmp.effects.prev = new Literal();
                if (m.connective == NOT)
                {
                    tmp.effects.prev.negated = true;
                    tmp.effects.prev.fact = make_Fact(m.sons, num_vars + tmp.num_vars);
                    if ((tmp.effects.prev.fact).predicate == 0)
                    {
                        FFUtilities.Write("\n\nequality in effect! check input files!\n\n");
                        Exit(1);
                    }
                }
                else
                {
                    tmp.effects.prev.negated = false;
                    tmp.effects.prev.fact = make_Fact( m, num_vars + tmp.num_vars);
                    if ((tmp.effects.prev.fact).predicate == 0)
                    {
                        FFUtilities.Write("\n\nequality in effect! check input files!\n\n");
                        Exit(1);
                    }
                }
                tmp.effects.prev.next = tmp.effects;
                tmp.effects = tmp.effects.prev;
            }

            return tmp;

        }











        /*************************
         * INERTIA PREPROCESSING *
         *************************/











        public  void do_inertia_preprocessing_step_1()

        {

            int i, j;
            Facts f;

            collect_inertia_information();

            if (gcmd_line.display_info == 105)
            {
                FFUtilities.Write("\n\npredicates inertia info:");
                for (i = 0; i < FF.DP.gnum_predicates; i++)
                {
                    FFUtilities.Write("\n%3d -. %s: ", i, FF.DP.gpredicates[i]);
                    FFUtilities.Write(" is %s, %s",
                       FF.Inertia.gis_added[i] ? "ADDED" : "NOT ADDED",
                       FF.Inertia.gis_deleted[i] ? "DELETED" : "NOT DELETED");
                }
                FFUtilities.Write("\n\n");
            }

            split_initial_state();

            if (gcmd_line.display_info == 106)
            {
                FFUtilities.Write("\n\nsplitted initial state is:");
                FFUtilities.Write("\nindividual predicates:");
                for (i = 0; i < FF.DP.gnum_predicates; i++)
                {
                    FFUtilities.Write("\n\n%s:" + FF.DP.gpredicates[i]);
                    if (!FF.Inertia.gis_added[i] &&
                     !FF.Inertia.gis_deleted[i])
                    {
                        FFUtilities.Write(" ---  ");
                    }
                    for (j = 0; j < FF.DP.gnum_initial_predicate[i]; j++)
                    {
                        FFUtilities.Write("\n");
                        print_Fact(FF.DP.ginitial_predicate[i,j]);
                    }
                }
                FFUtilities.Write("\n\nnon public  part:");
                for (f = FF.DP.ginitial; f!= null; f = f.next)
                {
                    FFUtilities.Write("\n");
                    print_Fact(f.fact);
                }

                FFUtilities.Write("\n\nextended types table:");
                for (i = 0; i < FF.DP.gnum_types; i++)
                {
                    FFUtilities.Write("\n" + i + " - ");
                    if (FF.Inertia.gpredicate_to_type[i] == -1)
                    {
                        FFUtilities.Write(" " + FF.DP.gtype_names[i]);
                    }
                    else
                    {
                        FFUtilities.Write("UNARY INERTIA TYPE (%s) ", FF.DP.gpredicates[FF.Inertia.gpredicate_to_type[i]]);
                    }
                    for (j = 0; j < FF.DP.gtype_size[i]; j++)
                    {
                        FFUtilities.Write(" " + FF.DP.gtype_consts[i,j]);
                    }
                }
            }

        }



        public  void collect_inertia_information()

        {

            int i;
            Effect e;
            Literal l;

            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                FF.Inertia.gis_added[i] = false;
                FF.Inertia.gis_deleted[i] = false;
            }

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                for (e = FF.DP.goperators[i].effects; e != null; e = e.next)
                {
                    for (l = e.effects; l != null; l = l.next)
                    {
                        if (l.negated)
                        {
                            FF.Inertia.gis_deleted[l.fact.predicate] = true;
                        }
                        else
                        {
                            FF.Inertia.gis_added[l.fact.predicate] = true;
                        }
                    }
                }
            }

        }



        public  void split_initial_state()

        {

            int i, j, p, t;
            Facts tmp;

            for (i = 0; i < Constants.MAX_PREDICATES; i++)
            {
                FF.Inertia.gtype_to_predicate[i] = -1;
            }
            for (i = 0; i < Constants.MAX_TYPES; i++)
            {
                FF.Inertia.gpredicate_to_type[i] = -1;
            }

            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                if (!FF.Inertia.gis_added[i] &&
                 !FF.Inertia.gis_deleted[i] &&
                 FF.DP.garity[i] == 1)
                {
                    if (FF.DP.gnum_types == Constants.MAX_TYPES)
                    {
                        FFUtilities.Write("\ntoo many (inferred) types! increase Constants.MAX_TYPES (currently %d)\n\n",
                               Constants.MAX_TYPES);
                        Exit(1);
                    }
                    FF.Inertia.gtype_to_predicate[i] = FF.DP.gnum_types;
                    FF.Inertia.gpredicate_to_type[FF.DP.gnum_types] = i;
                    FF.DP.gtype_names[FF.DP.gnum_types] = null;
                    FF.DP.gtype_size[FF.DP.gnum_types] = 0;
                    for (j = 0; j < Constants.MAX_CONSTANTS; j++)
                    {
                        FF.DP.gis_member[j,FF.DP.gnum_types] = false;
                    }
                    FF.DP.gnum_types++;
                }
            }


            /* double size of predicates table as each predicate miFF.Search.gHt need
             * to be translated to NOT-p
             */
            //Main.DP.ginitial_predicate = (Fact*)calloc(Main.DP.gnum_predicates * 2, sizeof(Fact));
            //Main.DP.gnum_initial_predicate = (int*)calloc(Main.DP.gnum_predicates * 2, sizeof(int));
            FF.DP.gnum_initial_predicate = new int[FF.DP.gnum_predicates * 2];
            for (i = 0; i < FF.DP.gnum_predicates * 2; i++)
            {
                FF.DP.gnum_initial_predicate[i] = 0;
            }
            int max = 0;
            for (i = 0; i < FF.DP.gnum_full_initial; i++)
            {
                p = FF.DP.gfull_initial[i].predicate;
                FF.DP.gnum_initial_predicate[p]++;
                if (FF.DP.gnum_initial_predicate[p] > max)
                    max = FF.DP.gnum_initial_predicate[p];
            }
            //FF.DP.ginitial_predicate = new Fact[FF.DP.gnum_predicates * 2, max];
            FF.DP.ginitial_predicate = new Array2D<Fact>(FF.DP.gnum_predicates * 2);
            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                //Main.DP.ginitial_predicate[i] = (Fact)calloc(Main.DP.gnum_initial_predicate[i], sizeof(Fact));
                FF.DP.ginitial_predicate[i] = new Fact[max];
                FF.DP.gnum_initial_predicate[i] = 0;
            }
            FF.DP.ginitial = null;
            FF.DP.gnum_initial = 0;

            for (i = 0; i < FF.DP.gnum_full_initial; i++)
            {
                p = FF.DP.gfull_initial[i].predicate;

                //Utilities.Write("p=" + p + " args:");
                FF.DP.ginitial_predicate[p, FF.DP.gnum_initial_predicate[p]] = new Fact();
                FF.DP.ginitial_predicate[p, FF.DP.gnum_initial_predicate[p]].predicate = p;
                for (j = 0; j < FF.DP.garity[p]; j++)
                {
                    FF.DP.ginitial_predicate[p,FF.DP.gnum_initial_predicate[p]].args[j] = FF.DP.gfull_initial[i].args[j];
                    //Utilities.Write("  " + Main.DP.gfull_initial[i].args[j]);
                }
                //Utilities.WriteLine();

                FF.DP.gnum_initial_predicate[p]++;
                if (FF.Inertia.gis_added[p] ||
                 FF.Inertia.gis_deleted[p])
                {
                    tmp = new Facts();
                    tmp.fact.predicate = p;
                    for (j = 0; j < FF.DP.garity[p]; j++)
                    {
                        tmp.fact.args[j] = FF.DP.gfull_initial[i].args[j];
                    }
                    tmp.next = FF.DP.ginitial;
                    FF.DP.ginitial = tmp;
                    FF.DP.gnum_initial++;
                }
                else
                {
                    if (FF.DP.garity[p] == 1)
                    {
                        t = FF.Inertia.gtype_to_predicate[p];
                        if (FF.DP.gtype_size[t] == Constants.MAX_TYPE)
                        {
                            FFUtilities.Write("\ntoo many consts in type %s! increase Constants.MAX_TYPE (currently %d)\n\n",
                               FF.DP.gtype_names[t], Constants.MAX_TYPE);
                            Exit(1);
                        }
                        if (!FF.DP.gis_member[FF.DP.gfull_initial[i].args[0],FF.DP.gpredicates_args_type[p,0]])
                        {
                            FFUtilities.Write("\ntype mismatch in initial state! %s as arg 0 of %s\n\n",
                               FF.DP.gconstants[FF.DP.gfull_initial[i].args[0]], FF.DP.gpredicates[p]);
                            Exit(1);
                        }
                        FF.DP.gtype_consts[t,FF.DP.gtype_size[t]++] = FF.DP.gfull_initial[i].args[0];
                        FF.DP.gis_member[FF.DP.gfull_initial[i].args[0],t] = true;
                    }
                }
            }

        }











        /******************************
         * NORMALIZE ALL PL1 FORMULAE *
         ******************************/












        public  void normalize_all_wffs()

        {

            int i;
            Effect e;

            simplify_wff(FF.DP.ggoal);
            remove_unused_vars_in_wff(FF.DP.ggoal);
            expand_quantifiers_in_wff(FF.DP.ggoal, -1, -1);
            NOTs_down_in_wff(FF.DP.ggoal);
            cleanup_wff(FF.DP.ggoal);
            if (FF.DP.ggoal.connective == TRU)
            {
                FFUtilities.Write("\nff: normalize: goal can be simplified to true. The empty plan solves it\n\n");
                Exit(1);
            }
            if (FF.DP.ggoal.connective == FAL)
            {
                FFUtilities.Write("\nff: goal can be simplified to false. No plan will solve it\n\n");
                Exit(1);
            }
            /* put goal into DNF riFF.Search.gHt away: fully instantiated already
             */
            dnf(FF.DP.ggoal);
            cleanup_wff(FF.DP.ggoal);

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                simplify_wff((FF.DP.goperators[i].preconds));
                remove_unused_vars_in_wff((FF.DP.goperators[i].preconds));
                expand_quantifiers_in_wff((FF.DP.goperators[i].preconds), -1, -1);
                NOTs_down_in_wff((FF.DP.goperators[i].preconds));
                cleanup_wff((FF.DP.goperators[i].preconds));

                for (e = FF.DP.goperators[i].effects; e != null; e = e.next)
                {
                    simplify_wff((e.conditions));
                    remove_unused_vars_in_wff((e.conditions));
                    expand_quantifiers_in_wff((e.conditions), -1, -1);
                    NOTs_down_in_wff((e.conditions));
                    cleanup_wff((e.conditions));
                }
            }

            if (gcmd_line.display_info == 107)
            {
                FFUtilities.Write("\n\ndomain with normalized PL1 formula:");

                FFUtilities.Write("\n\noperators are:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");

                FFUtilities.Write("\n\ngoal is:\n");
                Output.print_Wff(FF.DP.ggoal, 0);
            }

        }



        public  void remove_unused_vars_in_wff(WffNode w)

        {

            WffNode tmp;
            WffNode i;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    remove_unused_vars_in_wff((w.son));
                    if (!var_used_in_wff(FFUtilities.ENCODE_VAR(w.var), w.son))
                    {
                        decrement_inferior_vars(w.var, w.son);
                        w.connective = w.son.connective;
                        w.var = w.son.var;
                        w.var_type = w.son.var_type;
                        if (w.var_name != null)
                        {
                            ////free(w.var_name);
                            
                        }
                      w.var_name = w.son.var_name;
                        w.sons = w.son.sons;
                        if (w.fact != null)
                        {
                            ////free(w.fact);

                        }
                      w.fact = w.son.fact;
                        tmp = w.son;
                        w.son = w.son.son;
                        ////free(tmp);
                    }
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        remove_unused_vars_in_wff(i);
                    }
                    break;
                case NOT:
                    remove_unused_vars_in_wff((w.son));
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: remove var, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  bool var_used_in_wff(int code_var, WffNode w)

        {

            WffNode i;
            int j;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    return var_used_in_wff(code_var, w.son);
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        if (var_used_in_wff(code_var, i))
                        {
                            return true;
                        }
                    }
                    return false;
                case NOT:
                    return var_used_in_wff(code_var, w.son);
                case ATOM:
                    for (j = 0; j < FF.DP.garity[w.fact.predicate]; j++)
                    {
                        if (w.fact.args[j] >= 0)
                        {
                            continue;
                        }
                        if (w.fact.args[j] == code_var)
                        {
                            return true;
                        }
                    }
                    return false;
                case TRU:
                case FAL:
                    return false;
                default:
                    FFUtilities.Write("\nwon't get here: var used ?, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }
            return false;

        }



        public  void decrement_inferior_vars(int var, WffNode w)

        {

            WffNode i;
            int j;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    w.var--;
                    decrement_inferior_vars(var, w.son);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        decrement_inferior_vars(var, i);
                    }
                    break;
                case NOT:
                    decrement_inferior_vars(var, w.son);
                    break;
                case ATOM:
                    for (j = 0; j < FF.DP.garity[w.fact.predicate]; j++)
                    {
                        if (w.fact.args[j] >= 0)
                        {
                            continue;
                        }
                        if (FFUtilities.DECODE_VAR(w.fact.args[j]) > var)
                        {
                            w.fact.args[j]++;
                        }
                    }
                    break;
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: decrement, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  void simplify_wff(WffNode w)

        {

            WffNode i, tmp;
            int m;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    simplify_wff((w.son));
                    if (w.son.connective == TRU ||
                     w.son.connective == FAL)
                    {
                        w.connective = w.son.connective;
                        ////free(w.son);
                        w.son = null;
                        if (w.var_name != null)
                        {
                            ////free(w.var_name);
                        }
                    }
                    break;
                case AND:
                    m = 0;
                    i = w.sons;
                    while (i != null)
                    {
                        simplify_wff(i);
                        if (i.connective == FAL)
                        {
                            w.connective = FAL;
                            //free_WffNode(w.sons);
                            w.sons = null;
                            return;
                        }
                        if (i.connective == TRU)
                        {
                            if (i.prev != null)
                            {
                                i.prev.next = i.next;
                            }
                            else
                            {
                                w.sons = i.next;
                            }
                            if (i.next != null)
                            {
                                i.next.prev = i.prev;
                            }
                            tmp = i;
                            i = i.next;
                            //free(tmp);
                            continue;
                        }
                        i = i.next;
                        m++;
                    }
                    if (m == 0)
                    {
                        w.connective = TRU;
                        //free_WffNode(w.sons);
                        w.sons = null;
                    }
                    if (m == 1)
                    {
                        w.connective = w.sons.connective;
                        w.var = w.sons.var;
                        w.var_type = w.sons.var_type;
                        if (w.var_name != null)
                        {
                            //free(w.var_name);
                        }
                      w.var_name = w.sons.var_name;
                        w.son = w.sons.son;
                        if (w.fact != null)
                        {
                            //free(w.fact);
                        }
                      w.fact = w.sons.fact;
                        tmp = w.sons;
                        w.sons = w.sons.sons;
                        //free(tmp);
                    }
                    break;
                case OR:
                    m = 0;
                    i = w.sons;
                    while (i != null)
                    {
                        simplify_wff(i);
                        if (i.connective == TRU)
                        {
                            w.connective = TRU;
                            //free_WffNode(w.sons);
                            w.sons = null;
                            return;
                        }
                        if (i.connective == FAL)
                        {
                            if (i.prev != null)
                            {
                                i.prev.next = i.next;
                            }
                            else
                            {
                                w.sons = i.next;
                            }
                            if (i.next != null)
                            {
                                i.next.prev = i.prev;
                            }
                            tmp = i;
                            i = i.next;
                            //free(tmp);
                            continue;
                        }
                        i = i.next;
                        m++;
                    }
                    if (m == 0)
                    {
                        w.connective = FAL;
                        //free_WffNode(w.sons);
                        w.sons = null;
                    }
                    if (m == 1)
                    {
                        w.connective = w.sons.connective;
                        w.var = w.sons.var;
                        w.var_type = w.sons.var_type;
                        if (w.var_name != null)
                        {
                            //free(w.var_name);
                        }
                      w.var_name = w.sons.var_name;
                        w.son = w.sons.son;
                        if (w.fact != null)
                        {
                            //free(w.fact);
                        }
                      w.fact = w.sons.fact;
                        tmp = w.sons;
                        w.sons = w.sons.sons;
                        //free(tmp);
                    }
                    break;
                case NOT:
                    simplify_wff((w.son));
                    if (w.son.connective == TRU ||
                     w.son.connective == FAL)
                    {
                        w.connective = (w.son.connective == TRU) ? FAL : TRU;
                        //free(w.son);
                        w.son = null;
                    }
                    break;
                case ATOM:
                    if (w.visited)
                    {
                        /* already seen and not changed
                         */
                        break;
                    }
                    if (!possibly_negative(w.fact))
                    {
                        w.connective = TRU;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
                    if (!possibly_positive(w.fact))
                    {
                        w.connective = FAL;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
              w.visited = true;
                    break;
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: simplify, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  void expand_quantifiers_in_wff(WffNode w, int var, int constant)

        {

            WffNode r = null, tmp, i;
            int j, l;
            bool change;

            if (w == null)
            {
                return;
            }

            switch (w.connective)
            {
                case ALL:
                case EX:
                    if (var != -1)
                    {/* depth first: upper node is active */
                        expand_quantifiers_in_wff((w.son), var, constant);
                        return;
                    }

              w.connective = (w.connective == ALL) ? AND : OR;
                    for (j = 0; j < FF.DP.gtype_size[w.var_type]; j++)
                    {
                        tmp = copy_Wff(w.son);
                        expand_quantifiers_in_wff(tmp, w.var, FF.DP.gtype_consts[w.var_type,j]);
                        tmp.next = r;
                        if (r != null)
                        {
                            r.prev = tmp;
                        }
                        r = tmp;
                    }

                    //free_WffNode(w.son);
                    w.sons = r;
                    w.var = -1;
                    w.var_type = -1;
                    if (w.var_name != null)
                    {
                        //free(w.var_name);
                    }
              w.var_name = null;

                    /* now make all sons expand their quantifiers
                     */
                    for (i = w.sons; i != null; i = i.next)
                    {
                        expand_quantifiers_in_wff(i, -1, -1);
                    }
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        expand_quantifiers_in_wff(i, var, constant);
                    }
                    break;
                case NOT:
                    expand_quantifiers_in_wff((w.son), var, constant);
                    break;
                case ATOM:
                    if (var == -1)
                    {
                        break;
                    }

                    change = false;
                    for (l = 0; l < FF.DP.garity[w.fact.predicate]; l++)
                    {
                        if (w.fact.args[l] == FFUtilities.ENCODE_VAR(var))
                        {
                            w.fact.args[l] = constant;
                            change = true;
                        }
                    }
                    if (!change && w.visited)
                    {
                        /* we did not change anything and we've already seen that node
                         * -. it cant be simplified
                         */
                        break;
                    }
                    if (!possibly_negative(w.fact))
                    {
                        w.connective = TRU;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
                    if (!possibly_positive(w.fact))
                    {
                        w.connective = FAL;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
              w.visited = true;
                    break;
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: expansion, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  WffNode copy_Wff(WffNode w)

        {

            WffNode tmp, tmp2, i;
            int j;

            tmp = new WffNode(w.connective);

            switch (w.connective)
            {
                case ALL:
                case EX:
                    tmp.var = w.var;
                    tmp.var_type = w.var_type;
                    tmp.son = copy_Wff(w.son);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        tmp2 = copy_Wff(i);
                        if (tmp.sons != null)
                        {
                            tmp.sons.prev = tmp2;
                        }
                        tmp2.next = tmp.sons;
                        tmp.sons = tmp2;
                    }
                    break;
                case NOT:
                    tmp.son = copy_Wff(w.son);
                    break;
                case ATOM:
                    tmp.fact = new Fact();
                    tmp.fact.predicate = w.fact.predicate;
                    for (j = 0; j < FF.DP.garity[w.fact.predicate]; j++)
                    {
                        tmp.fact.args[j] = w.fact.args[j];
                    }
                    tmp.visited = w.visited;
                    break;
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: copy, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

            return tmp;

        }



        public  bool possibly_positive(Fact f)

        {

            int i;

            if (FF.Inertia.gis_added[f.predicate])
            {
                return true;
            }

            for (i = 0; i < FF.DP.gnum_initial_predicate[f.predicate]; i++)
            {
                if (matches(f, (FF.DP.ginitial_predicate[f.predicate,i])))
                {
                    return true;
                }
            }

            return false;

        }



        public  bool possibly_negative(Fact f)

        {

            int i;

            if (FF.Inertia.gis_deleted[f.predicate])
            {
                return true;
            }

            for (i = 0; i < FF.DP.garity[f.predicate]; i++)
            {
                if (f.args[i] < 0)
                {
                    return true;
                }
            }

            for (i = 0; i < FF.DP.gnum_initial_predicate[f.predicate]; i++)
            {
                if (matches(f, (FF.DP.ginitial_predicate[f.predicate,i])))
                {
                    return false;
                }
            }

            return true;

        }



        public  bool matches(Fact f1, Fact f2)

        {

            int i;

            for (i = 0; i < FF.DP.garity[f1.predicate]; i++)
            {
                if (f1.args[i] >= 0)
                {
                    if (f2.args[i] >= 0 &&
                     f1.args[i] != f2.args[i])
                    {
                        return false;
                    }
                }
            }

            return true;

        }



        public  void cleanup_wff(WffNode w)

        {

            merge_ANDs_and_ORs_in_wff(w);
            detect_tautologies_in_wff(w);
            simplify_wff(w);
            detect_tautologies_in_wff(w);
            merge_ANDs_and_ORs_in_wff(w);

        }



        public  void detect_tautologies_in_wff(WffNode w)

        {

            WffNode i, j, tmp;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    detect_tautologies_in_wff((w.son));
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        detect_tautologies_in_wff(i);
                    }
                    for (i = w.sons; i != null && i.next != null; i = i.next)
                    {
                        j = i.next;
                        while (j != null)
                        {
                            if (are_identical_ATOMs(i, j))
                            {
                                j.prev.next = j.next;
                                if (j.next != null)
                                {
                                    j.next.prev = j.prev;
                                }
                                tmp = j;
                                j = j.next;
                                if (tmp.fact != null)
                                {
                                    //free(tmp.fact);
                                }
                                //free(tmp);
                                continue;
                            }
                            if (i.connective == NOT &&
                                 are_identical_ATOMs(i.son, j))
                            {
                                w.connective = (w.connective == AND) ? FAL : TRU;
                                //free_WffNode(w.son);
                                w.son = null;
                                return;
                            }
                            if (j.connective == NOT &&
                                 are_identical_ATOMs(i, j.son))
                            {
                                w.connective = (w.connective == AND) ? FAL : TRU;
                                //free_WffNode(w.son);
                                w.son = null;
                                return;
                            }
                            j = j.next;
                        }
                    }
                    break;
                case NOT:
                    detect_tautologies_in_wff((w.son));
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: tautologies, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  bool are_identical_ATOMs(WffNode w1, WffNode w2)

        {

            int i;

            if (w1.connective != ATOM ||
                 w2.connective != ATOM)
            {
                return false;
            }

            if (w1.fact.predicate != w2.fact.predicate)
            {
                return false;
            }

            for (i = 0; i < FF.DP.garity[w1.fact.predicate]; i++)
            {
                if (w1.fact.args[i] != w2.fact.args[i])
                {
                    return false;
                }
            }

            return true;

        }



        public  void merge_ANDs_and_ORs_in_wff(WffNode w)

        {

            WffNode i, j, tmp;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    merge_ANDs_and_ORs_in_wff((w.son));
                    break;
                case AND:
                case OR:
                    i = w.sons;
                    while (i != null)
                    {
                        merge_ANDs_and_ORs_in_wff(i);
                        if (i.connective == w.connective)
                        {
                            if (!(i.sons != null))
                            {
                                if (i.next != null)
                                {
                                    i.next.prev = i.prev;
                                }
                                if (i.prev != null)
                                {
                                    i.prev.next = i.next;
                                }
                                else
                                {
                                    w.sons = i.next;
                                }
                                tmp = i;
                                i = i.next;
                                //free(tmp);
                                continue;
                            }
                            for (j = i.sons; j.next != null; j = j.next) ;
                            j.next = i.next;
                            if (i.next != null)
                            {
                                i.next.prev = j;
                            }
                            if (i.prev != null)
                            {
                                i.prev.next = i.sons;
                                i.sons.prev = i.prev;
                            }
                            else
                            {
                                w.sons = i.sons;
                            }
                            tmp = i;
                            i = i.next;
                            //free(tmp);
                            continue;
                        }
                        i = i.next;
                    }
                    break;
                case NOT:
                    merge_ANDs_and_ORs_in_wff((w.son));
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: merge, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  void NOTs_down_in_wff(WffNode w)

        {

            WffNode tmp1, tmp2, i;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\ntrying to put nots down in quantified formula! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        NOTs_down_in_wff(i);
                    }
                    break;
                case NOT:
                    if (w.son.connective == NOT)
                    {
                        w.connective = w.son.son.connective;
                        w.fact = w.son.son.fact;
                        tmp1 = w.son;
                        tmp2 = w.son.son;
                        w.sons = w.son.son.sons;
                        w.son = w.son.son.son;
                        //free(tmp1);
                        //free(tmp2);
                        NOTs_down_in_wff(w);
                        break;
                    }
                    if (w.son.connective == AND ||
                     w.son.connective == OR)
                    {
                        w.connective = (w.son.connective == AND) ? OR : AND;
                        w.sons = w.son.sons;
                        //free(w.son);
                        w.son = null;
                        for (i = w.sons; i != null; i = i.next)
                        {
                            tmp1 = new WffNode(i.connective);
                            tmp1.son = i.son;
                            tmp1.sons = i.sons;
                            tmp1.fact = i.fact;
                            i.connective = NOT;
                            i.son = tmp1;
                            i.sons = null;
                            i.fact = null;
                            NOTs_down_in_wff(i);
                        }
                        break;
                    }
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: nots down, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }


        }











        /****************************************************
         * NEGATIVE PRE- AND EFFECT- CONDITIONS TRANSLATION *
         ****************************************************/








        public  int[] lconsts = new int[Constants.MAX_ARITY];








        public  void translate_negative_preconds()

        {

            int i, j;
            Effect e;
            Facts f;

            while (introduce_derived_translate_op(FF.DP.ggoal)) ;

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                while (introduce_derived_translate_op(FF.DP.goperators[i].preconds)) ;

                for (e = FF.DP.goperators[i].effects; e != null; e = e.next)
                {
                    while (introduce_derived_translate_op(e.conditions)) ;
                }
            }

            if (gcmd_line.display_info == 108)
            {
                FFUtilities.Write("\n\ndomain with new axiom ops is, (pre) stratum 0:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    if (FF.DP.goperators[i].stratum != 0) continue;
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");
                FFUtilities.Write("\n\ndomain with new axiom ops is, (pre) stratum 1:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    if (FF.DP.goperators[i].stratum != 1) continue;
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");
                //fflush(stdout);
            }

            /* the new ops are introduced; now simply apply std methodology
             * for assigning strata. DOES THIS WORK???
             */
            assign_axiom_strata();

            if (gcmd_line.display_info == 108)
            {
                FFUtilities.Write("\n\ndomain with new axiom ops is, stratum 0:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    if (FF.DP.goperators[i].stratum != 0) continue;
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");
                FFUtilities.Write("\n\ndomain with new axiom ops is, stratum 1:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    if (FF.DP.goperators[i].stratum != 1) continue;
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");
               //fflush(stdout);
            }

            while (translate_one_negative_cond(FF.DP.ggoal)) ;

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                while (translate_one_negative_cond(FF.DP.goperators[i].preconds)) ;

                for (e = FF.DP.goperators[i].effects; e != null; e = e.next)
                {
                    while (translate_one_negative_cond(e.conditions)) ;
                }
            }

            if (gcmd_line.display_info == 108)
            {
                FFUtilities.Write("\n\ndomain with translated negative conds:");

                FFUtilities.Write("\n\noperators are:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");

                FFUtilities.Write("\ninitial state is:\n");
                for (f = FF.DP.ginitial; f != null; f = f.next)
                {
                    FFUtilities.Write("\n");
                    print_Fact(f.fact);
                }
                FFUtilities.Write("\n\n");

                FFUtilities.Write("\n\nindividual predicates:\n");
                for (i = 0; i < FF.DP.gnum_predicates; i++)
                {
                    FFUtilities.Write("\n\n%s:", FF.DP.gpredicates[i]);
                    if (!FF.Inertia.gis_added[i] &&
                     !FF.Inertia.gis_deleted[i])
                    {
                        FFUtilities.Write(" ---  ");
                    }
                    for (j = 0; j < FF.DP.gnum_initial_predicate[i]; j++)
                    {
                        FFUtilities.Write("\n");
                        print_Fact((FF.DP.ginitial_predicate[i,j]));
                    }
                }
                FFUtilities.Write("\n\n");

                FFUtilities.Write("\n\ngoal is:\n");
                print_Wff(FF.DP.ggoal, 0);
                FFUtilities.Write("\n\n");
                //fflush(stdout);
            }

        }



       public  bool translate_one_negative_cond(WffNode w)

        {

            WffNode i;
            int p, j, k, m;
            Effect e;
            Literal l, tmp;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\ntranslating NOT in quantified formula! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        if (translate_one_negative_cond(i))
                        {
                            return true;
                        }
                    }
                    return false;
                case NOT:
                    if (w.son.fact.predicate == -1)
                    {
                        return false;
                    }
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    return false;
                default:
                    FFUtilities.Write("\nwon't get here: remove var, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }


            if (FF.DP.gnum_predicates == Constants.MAX_PREDICATES)
            {
                FFUtilities.Write("\ntoo many predicates in translation! increase Constants.MAX_PREDICATES (currently %d)\n\n",
                   Constants.MAX_PREDICATES);
                Exit(1);
            }
            p = w.son.fact.predicate;
            FF.DP.gpredicates[FF.DP.gnum_predicates] = "NOT-" + FF.DP.gpredicates[p];
            FF.DP.garity[FF.DP.gnum_predicates] = FF.DP.garity[p];
            FF.DP.gderived[FF.DP.gnum_predicates] = FF.DP.gderived[p];
            for (j = 0; j < FF.DP.garity[p]; j++)
            {
                FF.DP.gpredicates_args_type[FF.DP.gnum_predicates,j] =
                  FF.DP.gpredicates_args_type[p,j];
            }
            FF.Inertia.gis_added[FF.DP.gnum_predicates] = false;
            FF.Inertia.gis_deleted[FF.DP.gnum_predicates] = false;
            m = 1;
            for (j = 0; j < FF.DP.garity[FF.DP.gnum_predicates]; j++)
            {
                m *= FF.DP.gtype_size[FF.DP.gpredicates_args_type[FF.DP.gnum_predicates,j]];
            }
            //already initialized in split_initial_state???
            FF.DP.ginitial_predicate[FF.DP.gnum_predicates]= new Fact[m];
            FF.DP.gnum_predicates++;


            replace_not_p_with_n_in_wff(p, FF.DP.gnum_predicates - 1, FF.DP.ggoal);

            for (j = 0; j < FF.DP.gnum_operators; j++)
            {
                replace_not_p_with_n_in_wff(p, FF.DP.gnum_predicates - 1,
                             (FF.DP.goperators[j].preconds));

                for (e = FF.DP.goperators[j].effects; e != null; e = e.next)
                {
                    replace_not_p_with_n_in_wff(p, FF.DP.gnum_predicates - 1,
                                 (e.conditions));
                    for (l = e.effects; l != null; l = l.next)
                    {
                        if (l.fact.predicate != p)
                        {
                            continue;
                        }
                        tmp = new Literal();
                        if (l.negated)
                        {
                            tmp.negated = false;
                            FF.Inertia.gis_added[FF.DP.gnum_predicates - 1] = true;
                        }
                        else
                        {
                            tmp.negated = true;
                            FF.Inertia.gis_deleted[FF.DP.gnum_predicates - 1] = true;
                        }
                        tmp.fact.predicate = FF.DP.gnum_predicates - 1;
                        for (k = 0; k < FF.DP.garity[p]; k++)
                        {
                            tmp.fact.args[k] = l.fact.args[k];
                        }
                        if (l.next != null)
                        {
                            tmp.next = l.next;
                            l.next.prev = tmp;
                        }
                        tmp.prev = l;
                        l.next = tmp;
                    }
                }
            }

            add_to_initial_state(p, FF.DP.gnum_predicates - 1, 0);

            return true;

        }


        bool first_call_introduce_derived_translate_op = true;
        bool[] had_introduce_derived_translate_op = new bool[Constants.MAX_PREDICATES];

        public  bool introduce_derived_translate_op(WffNode w)
        {
            WffNode i, tmpw;
            int p, j, k;
            Effect tmpe;
            Literal tmp;
            Operator tmpo;

            if (first_call_introduce_derived_translate_op)
            {
                for (j = 0; j < Constants.MAX_PREDICATES; j++)
                {
                    had_introduce_derived_translate_op[j] = false;
                }
                first_call_introduce_derived_translate_op = false;
            }

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\ntranslating NOT in quantified formula! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        if (introduce_derived_translate_op(i))
                        {
                            return true;
                        }
                    }
                    return false;
                case NOT:
                    if (w.son.fact.predicate == -1)
                    {
                        return false;
                    }
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    return false;
                default:
                    FFUtilities.Write("\nwon't get here: remove var, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

            p = w.son.fact.predicate;
            if (!FF.DP.gderived[p] || had_introduce_derived_translate_op[p])
            {
                return false;
            }
            had_introduce_derived_translate_op[p] = true;

            /* if it is a derived predicate then, additionally
             * (we keep the not-fts in ini in order to apublic  void
             * pruning mechanisms in instantiation)
             * introduce a new axiom-op  (derived  not-p  -pre-org)
             */
            /* find org axiom op
             */
            for (j = 0; j < FF.DP.gnum_operators; j++)
            {
                if (!FF.DP.goperators[j].axiom) continue;
                if (FF.DP.goperators[j].effects.effects.fact.predicate == p) break;
            }
            if (j == FF.DP.gnum_operators)
            {
                FFUtilities.Write("\n\ndidn't find deriving op for predicate %s?\n\n",
                   FF.DP.gpredicates[p]);
                Exit(1);
            }

            tmpo = new Operator(FF.DP.goperators[j].name, FF.DP.goperators[j].number_of_real_params);

            tmpo.axiom = true;
            tmpo.stratum = 1;
            for (k = 0; k < FF.DP.goperators[j].num_vars; k++)
            {
                //tmpo.var_names[k] = new_Token(strlen(Main.DP.goperators[j].var_names[k]) + 1);
                tmpo.var_names[k] = FF.DP.goperators[j].var_names[k];
                tmpo.var_types[k] = FF.DP.goperators[j].var_types[k];
            }
            tmpo.num_vars = FF.DP.goperators[j].num_vars;

            tmpw = new WffNode(NOT);
            tmpw.son = copy_Wff(FF.DP.goperators[j].preconds);
            simplify_wff(tmpw);
            remove_unused_vars_in_wff(tmpw);
            expand_quantifiers_in_wff(tmpw, -1, -1);
            NOTs_down_in_wff(tmpw);
            cleanup_wff(tmpw);
            tmpo.preconds = tmpw;

            tmpe = new Effect();
            tmpe.conditions = copy_Wff(FF.DP.goperators[j].effects.conditions);
            tmp = new Literal();
            tmp.negated = true;
            FF.Inertia.gis_deleted[p] = true;
            tmp.fact.predicate = p;
            for (k = 0; k < FF.DP.garity[p]; k++)
            {
                tmp.fact.args[k] = FF.DP.goperators[j].effects.effects.fact.args[k];
            }
            tmpe.effects = tmp;
            tmpo.effects = tmpe;

            FF.DP.goperators[FF.DP.gnum_operators++] = tmpo;

            return true;

        }



        public  void replace_not_p_with_n_in_wff(int p, int n, WffNode w)

        {

            WffNode i;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\nreplacing p with NOT-p in quantified formula! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        replace_not_p_with_n_in_wff(p, n, i);
                    }
                    break;
                case NOT:
                    if (w.son.fact.predicate == p)
                    {
                        w.connective = ATOM;
                        w.NOT_p = p;
                        w.fact = w.son.fact;
                        w.fact.predicate = n;
                        //free(w.son);
                        w.son = null;
                    }
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: replace p with NOT-p, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  void add_to_initial_state(int p, int n, int index)
        {

            int i, j;
            Facts tmp;

            if (index == FF.DP.garity[p])
            {
                /* see if contrary fact is there in ini
                 */
                for (i = 0; i < FF.DP.gnum_initial_predicate[p]; i++)
                {
                    for (j = 0; j < FF.DP.garity[p]; j++)
                    {
                        if (FF.DP.ginitial_predicate[p,i].args[j] != lconsts[j])
                        {
                            break;
                        }
                    }
                    if (j == FF.DP.garity[p])
                    {
                        break;
                    }
                }
                if (i < FF.DP.gnum_initial_predicate[p])
                {
                    return;
                }

                /* no: add new fact to ini
                 */
                FF.DP.ginitial_predicate[n, FF.DP.gnum_initial_predicate[n]] = new Fact();
                FF.DP.ginitial_predicate[n, FF.DP.gnum_initial_predicate[n]].predicate = n;
                for (i = 0; i < FF.DP.garity[n]; i++)
                {
                    FF.DP.ginitial_predicate[n,FF.DP.gnum_initial_predicate[n]].args[i] = lconsts[i];
                }
                FF.DP.gnum_initial_predicate[n]++;

                if (!FF.Inertia.gis_added[n] &&
                 !FF.Inertia.gis_deleted[n])
                {
                    return;
                }

                tmp = new Facts();
                tmp.fact.predicate = n;
                for (i = 0; i < FF.DP.garity[p]; i++)
                {
                    tmp.fact.args[i] = lconsts[i];
                }
                tmp.next = FF.DP.ginitial;
                FF.DP.ginitial = tmp;
                FF.DP.gnum_initial++;
                return;
            }

            for (i = 0; i < FF.DP.gtype_size[FF.DP.gpredicates_args_type[p,index]]; i++)
            {
                lconsts[index] = FF.DP.gtype_consts[FF.DP.gpredicates_args_type[p,index],i];
                add_to_initial_state(p, n, index + 1);
            }

        }

























        /**************************************************
         * AXIOM STRATA: WHICH ONES TO BE APPLIED FIRST?
         **************************************************/


















        public  void assign_axiom_strata()

        {

            int i, j, k, level;
            int[,] R;
            int[] stratum;
            int num_stratum;

            /*
            R = (int**)calloc(Main.DP.gnum_operators, sizeof(int*));
            for (i = 0; i < Main.DP.gnum_operators; i++)
            {
                R[i] = (int*)calloc(Main.DP.gnum_operators, sizeof(int));
                for (j = 0; j < Main.DP.gnum_operators; j++) R[i,j] = 0;
            }
            */
            R = new int[FF.DP.gnum_operators, FF.DP.gnum_operators];
            //stratum = (int*)calloc(Main.DP.gnum_operators, sizeof(int));
            stratum = new int[FF.DP.gnum_operators];

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (!FF.DP.goperators[i].axiom) continue;
                for (j = 0; j < FF.DP.gnum_operators; j++)
                {
                    if (!FF.DP.goperators[j].axiom) continue;
                    if (false && FF.DP.goperators[i].stratum == 0 &&
                     FF.DP.goperators[j].stratum == 1)
                    {
                        R[i,j] = 2;
                        continue;
                    }
                    if (FF.DP.goperators[i].stratum == 1 &&
                     FF.DP.goperators[j].stratum == 0)
                    {
                        continue;
                    }
                    if (FF.DP.goperators[i].stratum == 1 &&
                     FF.DP.goperators[j].stratum == 1)
                    {
                        continue;
                    }
                    if (i_effect_occurs_negatively_in_jpre(i, j))
                    {
                        R[i,j] = 2;
                    }
                    else
                    {
                        if (i_effect_occurs_positively_in_jpre(i, j))
                        {
                            if (R[i,j] < 1) R[i,j] = 1;
                        }
                    }
                }
            }


            for (j = 0; j < FF.DP.gnum_operators; j++)
            {
                if (!FF.DP.goperators[j].axiom) continue;
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    if (!FF.DP.goperators[i].axiom) continue;
                    for (k = 0; k < FF.DP.gnum_operators; k++)
                    {
                        if (!FF.DP.goperators[k].axiom) continue;
                        if (R[i,j] > 0 && R[j,k] > 0)
                        {
                            if (R[i,k] < R[i,j]) R[i,k] = R[i,j];
                            if (R[i,k] < R[j,k]) R[i,k] = R[j,k];
                        }
                    }
                }
            }


            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (!FF.DP.goperators[i].axiom) continue;
                if (R[i,i] == 2)
                {
                    FFUtilities.Write("\n\naxioms can not be stratified!! can't handle this planning task!\n\n");
                    Exit(1);
                }
            }


            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (!FF.DP.goperators[i].axiom)
                {
                    FF.DP.goperators[i].stratum = -1;
                    continue;
                }
                FF.DP.goperators[i].stratum = 0;
            }

            level = 1;
            while (true)
            {
                /* for all j remaining
                 */
                for (j = 0; j < FF.DP.gnum_operators; j++)
                {
                    if (FF.DP.goperators[j].stratum == 0) break;
                }
                if (j == FF.DP.gnum_operators) break;/* no such j: stop */

                /* build new stratum
                 */
                num_stratum = 0;
                for (j = 0; j < FF.DP.gnum_operators; j++)
                {
                    if (FF.DP.goperators[j].stratum != 0) continue;
                    for (i = 0; i < FF.DP.gnum_operators; i++)
                    {
                        if (FF.DP.goperators[i].stratum != 0) continue;
                        if (R[i,j] == 2) break;
                    }
                    if (i < FF.DP.gnum_operators) continue;
                    stratum[num_stratum++] = j;
                }
                for (i = 0; i < num_stratum; i++)
                {
                    FF.DP.goperators[stratum[i]].stratum = level;
                }
                level++;
            }
            FF.Planning.gnum_strata = level;

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                //free(R[i]);
            }
            //free(R);
            //free(stratum);


            if (gcmd_line.display_info == 130)
            {
                FFUtilities.Write("\n\nstratified operators:");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    FFUtilities.Write("\n\n\n------------------------------- OP %d", i);
                    print_Operator(FF.DP.goperators[i]);
                }
                FFUtilities.Write("\n\n");
            }

        }



        public  bool i_effect_occurs_negatively_in_jpre(int i, int j)

        {

            int p;
            WffNode w;
            bool result;

            p = FF.DP.goperators[i].effects.effects.fact.predicate;

            w = FF.DP.goperators[j].preconds;

            result = p_occurs_negatively_in_w(p, w);

            if (gcmd_line.debug >= 3)
            {
                if (result || gcmd_line.debug >= 4) FFUtilities.Write("\n\nderived predicate of OP %d, %s, ", i, FF.DP.gpredicates[p]);
                if (result)
                {
                    FFUtilities.Write("occurs negatively in prec OP %d", j);
                }
                else
                {
                    if (gcmd_line.debug >= 4) FFUtilities.Write("does not occur negatively in prec OP %d", j);
                }
            }

            return result;

        }



        public  bool p_occurs_negatively_in_w(int p, WffNode w)

        {

            WffNode i;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\nneg p occurence in quantified formula searched! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        if (p_occurs_negatively_in_w(p, i))
                        {
                            return true;
                        }
                    }
                    break;
                case NOT:
                    if (w.son == null ||
                     w.son.fact == null ||
                     w.son.connective != ATOM)
                    {
                        FFUtilities.Write("\nnon atomic NOT in neg p search! debug me\n\n");
                        Exit(1);
                    }
                    if (w.son.fact.predicate == p)
                    {
                        return true;
                    }
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: neg p search, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

            return false;

        }



        public  bool i_effect_occurs_positively_in_jpre(int i, int j)

        {

            int p;
            WffNode w;
            bool result;

            p = FF.DP.goperators[i].effects.effects.fact.predicate;

            w = FF.DP.goperators[j].preconds;

            result = p_occurs_positively_in_w(p, w);

            if (gcmd_line.debug >= 3)
            {
                if (result || gcmd_line.debug >= 4) FFUtilities.Write("\n\nderived predicate of OP %d, %s, ", i, FF.DP.gpredicates[p]);
                if (result)
                {
                    FFUtilities.Write("occurs positively in prec OP %d", j);
                }
                else
                {
                    if (gcmd_line.debug >= 4) FFUtilities.Write("does not occur positively in prec OP %d", j);
                }
            }

            return result;

        }



        public  bool p_occurs_positively_in_w(int p, WffNode w)

        {

            WffNode i;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\np occurence in quantified formula searched! debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        if (p_occurs_positively_in_w(p, i))
                        {
                            return true;
                        }
                    }
                    break;
                case ATOM:
                    if (w.fact == null)
                    {
                        FFUtilities.Write("\nnon atomic ATOM in p search! debug me\n\n");
                        Exit(1);
                    }
                    if (w.fact.predicate == p)
                    {
                        return true;
                    }
                    break;
                case NOT:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: p search, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

            return false;

        }
















        /*******************************************************************
         * SPLIT DOMAIN IN PREPARATION FOR SEPARATE INSTANTIATION ROUTINES *
         *******************************************************************/










        public  void split_domain()

        {

            int i, j, m, s = 0, a;
            Effect e;
            WffNode w, ww, www;
            NormOperator tmp_op;
            Fact tmp_ft;

            for (i = 0; i < Constants.MAX_TYPES; i++)
            {
                FF.Inertia.gnum_intersected_types[i] = -1;
            }

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if ((m = is_dnf(FF.DP.goperators[i].preconds)) != -1)
                {
                    for (e = FF.DP.goperators[i].effects; e != null; e = e.next)
                    {
                        if (is_dnf(e.conditions) == -1)
                        {
                            break;
                        }
                    }
                    if (e == null)
                    {
                        FF.DP.goperators[i].hard = false;
                        s += m;
                    }
                }
            }

            //Main.DP.FF.Search.gHard_operators = (Operator_pointer*)calloc(Constants.MAX_OPERATORS, sizeof(Operator));
            FF.DP.ghard_operators = new Operator[Constants.MAX_OPERATORS];
            FF.DP.gnum_hard_operators = 0;
            //Main.DP.geasy_operators = (NormOperator_pointer*)calloc(s, sizeof(NormOperator_pointer));
            FF.DP.geasy_operators = new NormOperator[s];
            FF.DP.gnum_easy_operators = 0;

            for (i = 0; i < FF.DP.gnum_operators; i++)
            {
                if (FF.DP.goperators[i].hard)
                {
                    FF.DP.ghard_operators[FF.DP.gnum_hard_operators++] = FF.DP.goperators[i];
                    continue;
                }
                w = FF.DP.goperators[i].preconds;
                switch (w.connective)
                {
                    case OR:
                        for (ww = w.sons; ww != null; ww = ww.next)
                        {
                            tmp_op = new NormOperator(FF.DP.goperators[i]);
                            if (ww.connective == AND)
                            {
                                m = 0;
                                for (www = ww.sons; www != null; www = www.next) m++;
                                tmp_op.preconds = new Fact[m];// (Fact)calloc(m, sizeof(Fact));
                                for (www = ww.sons; www != null; www = www.next)
                                {
                                    tmp_ft = (tmp_op.preconds[tmp_op.num_preconds]);
                                    tmp_ft.predicate = www.fact.predicate;
                                    a = FF.DP.garity[tmp_ft.predicate];
                                    for (j = 0; j < a; j++)
                                    {
                                        tmp_ft.args[j] = www.fact.args[j];
                                    }
                                    tmp_op.num_preconds++;
                                }
                            }
                            else
                            {
                                tmp_op.preconds = new Fact[1];// = new Fact[1];
                                tmp_ft = (tmp_op.preconds[0]);
                                tmp_ft.predicate = ww.fact.predicate;
                                a = FF.DP.garity[tmp_ft.predicate];
                                for (j = 0; j < a; j++)
                                {
                                    tmp_ft.args[j] = ww.fact.args[j];
                                }
                                tmp_op.num_preconds = 1;
                            }
                            make_normal_effects(tmp_op, FF.DP.goperators[i]);
                            FF.DP.geasy_operators[FF.DP.gnum_easy_operators++] = tmp_op;
                        }
                        break;
                    case AND:
                        tmp_op = new NormOperator(FF.DP.goperators[i]);
                        m = 0;
                        for (ww = w.sons; ww != null; ww = ww.next) m++;
                        tmp_op.preconds = new Fact[m];// (Fact)calloc(m, sizeof(Fact));
                        for (ww = w.sons; ww != null; ww = ww.next)
                        {
                            tmp_op.preconds[tmp_op.num_preconds] = new Fact();
                            tmp_ft = (tmp_op.preconds[tmp_op.num_preconds]);
                            tmp_ft.predicate = ww.fact.predicate;
                            a = FF.DP.garity[tmp_ft.predicate];
                            for (j = 0; j < a; j++)
                            {
                                tmp_ft.args[j] = ww.fact.args[j];
                            }
                            tmp_op.num_preconds++;
                        }
                        make_normal_effects(tmp_op, FF.DP.goperators[i]);
                        FF.DP.geasy_operators[FF.DP.gnum_easy_operators++] = tmp_op;
                        break;
                    case NOT:
                    case ATOM:
                        tmp_op = new NormOperator(FF.DP.goperators[i]);
                        tmp_op.preconds = new Fact[1];// = new Fact[1];
                        tmp_ft = tmp_op.preconds[0];
                        tmp_ft.predicate = w.fact.predicate;
                        a = FF.DP.garity[tmp_ft.predicate];
                        for (j = 0; j < a; j++)
                        {
                            tmp_ft.args[j] = w.fact.args[j];
                        }
                        tmp_op.num_preconds = 1;
                        make_normal_effects(tmp_op, FF.DP.goperators[i]);
                        FF.DP.geasy_operators[FF.DP.gnum_easy_operators++] = tmp_op;
                        break;
                    case TRU:
                        tmp_op = new NormOperator(FF.DP.goperators[i]);
                        make_normal_effects(tmp_op, FF.DP.goperators[i]);
                        FF.DP.geasy_operators[FF.DP.gnum_easy_operators++] = tmp_op;
                        break;
                    case FAL:
                        break;
                    default:
                        FFUtilities.Write("\nwon't get here: non OR, AND, ATOM, true, false in dnf. debug me\n\n");
                        Exit(1);
                        break;
                }
            }

            if (gcmd_line.display_info == 109)
            {
                FFUtilities.Write("\n\nsplitted operators are:\n");

                FFUtilities.Write("\nEASY:\n");
                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    print_NormOperator(FF.DP.geasy_operators[i]);
                }

                FFUtilities.Write("\n\n\nHARD:\n");
                for (i = 0; i < FF.DP.gnum_hard_operators; i++)
                {
                    print_Operator(FF.DP.ghard_operators[i]);
                }
            }

        }



        public  int is_dnf(WffNode w)

        {

            WffNode i;
            int s = 0;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\nchecking quantifier for dnf. debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        if (i.connective == ATOM ||
                         (i.connective == NOT &&
                           i.son.fact.predicate == -1))
                        {
                            continue;
                        }
                        return -1;
                    }
                    return 1;
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        s++;
                        if (i.connective == ATOM ||
                         (i.connective == NOT &&
                           i.son.fact.predicate == -1) ||
                         (i.connective == AND &&
                           is_dnf(i) != -1))
                        {
                            continue;
                        }
                        return -1;
                    }
                    return s;
                case NOT:
                    if (w.son.fact.predicate == -1)
                    {
                        return 1;
                    }
                    else
                    {
                        FFUtilities.Write("\nNOT with non eq - son in presimplified formula. debug me\n\n");
                        Exit(1);
                        break;
                    }
                case ATOM:
                case TRU:
                case FAL:
                    return 1;
                default:
                    FFUtilities.Write("\nwon't get here: check dnf, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }
            return 0;
        }



        public  void make_normal_effects(NormOperator nop, Operator op)

        {

            Effect e;
            NormEffect tmp_ef;
            WffNode w, ww, www;
            int j, a, m, ma, md;
            Literal l;
            Fact tmp_ft;

            for (e = op.effects; e != null; e = e.next)
            {
                w = e.conditions;
                switch (w.connective)
                {
                    case OR:
                        for (ww = w.sons; ww != null; ww = ww.next)
                        {
                            //tmp_ef = new NormEffect(e);
                            tmp_ef = new NormEffect(e);
                            if (ww.connective == AND)
                            {
                                m = 0;
                                for (www = ww.sons; www != null; www = www.next) m++;
                                tmp_ef.conditions = new InitializedArray<Fact>(m);
                                for (www = ww.sons; www != null; www = www.next)
                                {
                                    tmp_ft = (tmp_ef.conditions[tmp_ef.num_conditions]);
                                    tmp_ft.predicate = www.fact.predicate;
                                    a = FF.DP.garity[tmp_ft.predicate];
                                    for (j = 0; j < a; j++)
                                    {
                                        tmp_ft.args[j] = www.fact.args[j];
                                    }
                                    tmp_ef.num_conditions++;
                                }
                            }
                            else
                            {
                                tmp_ef.conditions = new InitializedArray<Fact>(1);
                                tmp_ft = (tmp_ef.conditions[0]);
                                tmp_ft.predicate = ww.fact.predicate;
                                a = FF.DP.garity[tmp_ft.predicate];
                                for (j = 0; j < a; j++)
                                {
                                    tmp_ft.args[j] = ww.fact.args[j];
                                }
                                tmp_ef.num_conditions = 1;
                            }
                            ma = 0;
                            md = 0;
                            for (l = e.effects; l != null; l = l.next)
                            {
                                if (l.negated)
                                {
                                    md++;
                                }
                                else
                                {
                                    ma++;
                                }
                            }
                            tmp_ef.adds = new InitializedArray<Fact>(ma);// new Fact[ma];
                            tmp_ef.dels = new InitializedArray<Fact>(md);// new Fact[md];
                            for (l = e.effects; l != null; l = l.next)
                            {
                                if (l.negated)
                                {
                                    tmp_ft = (tmp_ef.dels[tmp_ef.num_dels++]);
                                }
                                else
                                {
                                    tmp_ft = (tmp_ef.adds[tmp_ef.num_adds++]);
                                }
                                tmp_ft.predicate = l.fact.predicate;
                                for (j = 0; j < FF.DP.garity[tmp_ft.predicate]; j++)
                                {
                                    tmp_ft.args[j] = l.fact.args[j];
                                }
                            }
                            tmp_ef.next = nop.effects;
                            if (nop.effects != null)
                            {
                                nop.effects.prev = tmp_ef;
                            }
                            nop.effects = tmp_ef;
                        }
                        break;
                    case AND:
                        tmp_ef = new NormEffect(e);
                        m = 0;
                        for (ww = w.sons; ww != null; ww = ww.next) m++;
                        tmp_ef.conditions = new InitializedArray<Fact>(m);
                        for (ww = w.sons; ww != null; ww = ww.next)
                        {
                            tmp_ft = (tmp_ef.conditions[tmp_ef.num_conditions]);
                            tmp_ft.predicate = ww.fact.predicate;
                            a = FF.DP.garity[tmp_ft.predicate];
                            for (j = 0; j < a; j++)
                            {
                                tmp_ft.args[j] = ww.fact.args[j];
                            }
                            tmp_ef.num_conditions++;
                        }
                        ma = 0;
                        md = 0;
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                md++;
                            }
                            else
                            {
                                ma++;
                            }
                        }
                        tmp_ef.adds = new InitializedArray<Fact>(ma);
                        tmp_ef.dels = new InitializedArray<Fact>(md);
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                tmp_ft = (tmp_ef.dels[tmp_ef.num_dels++]);
                            }
                            else
                            {
                                tmp_ft = (tmp_ef.adds[tmp_ef.num_adds++]);
                            }
                            tmp_ft.predicate = l.fact.predicate;
                            for (j = 0; j < FF.DP.garity[tmp_ft.predicate]; j++)
                            {
                                tmp_ft.args[j] = l.fact.args[j];
                            }
                        }
                        tmp_ef.next = nop.effects;
                        if (nop.effects != null)
                        {
                            nop.effects.prev = tmp_ef;
                        }
                        nop.effects = tmp_ef;
                        break;
                    case NOT:
                    case ATOM:
                        tmp_ef = new NormEffect(e);
                        tmp_ef.conditions = new InitializedArray<Fact>(1);
                        tmp_ft = (tmp_ef.conditions[0]);
                        tmp_ft.predicate = w.fact.predicate;
                        a = FF.DP.garity[tmp_ft.predicate];
                        for (j = 0; j < a; j++)
                        {
                            tmp_ft.args[j] = w.fact.args[j];
                        }
                        tmp_ef.num_conditions = 1;
                        ma = 0;
                        md = 0;
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                md++;
                            }
                            else
                            {
                                ma++;
                            }
                        }
                        tmp_ef.adds = new InitializedArray<Fact>(ma);
                        tmp_ef.dels = new InitializedArray<Fact>(md);
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                tmp_ft = (tmp_ef.dels[tmp_ef.num_dels++]);
                            }
                            else
                            {
                                tmp_ft = (tmp_ef.adds[tmp_ef.num_adds++]);
                            }
                            tmp_ft.predicate = l.fact.predicate;
                            for (j = 0; j < FF.DP.garity[tmp_ft.predicate]; j++)
                            {
                                tmp_ft.args[j] = l.fact.args[j];
                            }
                        }
                        tmp_ef.next = nop.effects;
                        if (nop.effects != null)
                        {
                            nop.effects.prev = tmp_ef;
                        }
                        nop.effects = tmp_ef;
                        break;
                    case TRU:
                        tmp_ef = new NormEffect(e);
                        ma = 0;
                        md = 0;
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                md++;
                            }
                            else
                            {
                                ma++;
                            }
                        }
                        tmp_ef.adds = new InitializedArray<Fact>(ma);
                        tmp_ef.dels = new InitializedArray<Fact>(md);
                        for (l = e.effects; l != null; l = l.next)
                        {
                            if (l.negated)
                            {
                                tmp_ft = (tmp_ef.dels[tmp_ef.num_dels++]);
                            }
                            else
                            {
                                tmp_ft = (tmp_ef.adds[tmp_ef.num_adds++]);
                            }
                            tmp_ft.predicate = l.fact.predicate;
                            for (j = 0; j < FF.DP.garity[tmp_ft.predicate]; j++)
                            {
                                tmp_ft.args[j] = l.fact.args[j];
                            }
                        }
                        tmp_ef.next = nop.effects;
                        if (nop.effects != null)
                        {
                            nop.effects.prev = tmp_ef;
                        }
                        nop.effects = tmp_ef;
                        break;
                    case FAL:
                        break;
                    default:
                        FFUtilities.Write("\nwon't get here: non OR, AND, ATOM, true, false in dnf. debug me\n\n");
                        Exit(1);
                        break;
                }
            }

        }









        /*************************************************************************
         * ADDITIONAL: FULL DNF, only compute on fully instantiated formulae!!!! *
         *************************************************************************/










        /* dnf
         */

        public  WffNode lhitting_sets;
        public  WffNode[] lset;
        public  int lmax_set;




            bool first_call_dnf = true;


        public  void dnf(WffNode w)
        {
            if (first_call_dnf)
            {
                //lset = (WffNode_pointer*)calloc(Constants.MAX_HITTING_SET_DEFAULT, sizeof(WffNode_pointer));
                lset = new WffNode[Constants.MAX_HITTING_SET_DEFAULT];
                lmax_set = Constants.MAX_HITTING_SET_DEFAULT;
                first_call_dnf = false;
            }

            ANDs_below_ORs_in_wff(w);

        }



        public  void ANDs_below_ORs_in_wff(WffNode w)

        {

            WffNode i, tmp;
            int c, m;

            switch (w.connective)
            {
                case ALL:
                case EX:
                    FFUtilities.Write("\ntrying to put quantified formula into DNF! (ands down) debug me\n\n");
                    Exit(1);
                    break;
                case AND:
                    c = 0;
                    m = 0;
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        ANDs_below_ORs_in_wff(i);
                        if (i.connective == OR)
                        {
                            c++;
                        }
                        m++;
                    }
                    if (c == 0)
                    {
                        /* no ORs as sons -. all sons are literals. OK
                         */
                        merge_next_step_ANDs_and_ORs_in_wff(w);
                        break;
                    }
                    /* crucial part: AND node, sons can be merged OR's.
                     * (i.e., sons are either literals or disjunctions of 
                     * conjunctions of literals)
                     * create OR node with one hitting set of w's sons for 
                     * each disjunct
                     */
                    lhitting_sets = null;
                    if (m > lmax_set)
                    {
                        //free(lset);
                        //lset = (WffNode_pointer*)calloc(m, sizeof(WffNode_pointer));
                        lset = new WffNode[m];
                        lmax_set = m;
                    }
                    collect_hitting_sets(w.sons, 0);
                    w.connective = OR;
                    tmp = w.sons;
                    w.sons = lhitting_sets;
                    //free_WffNode(tmp);
                    merge_next_step_ANDs_and_ORs_in_wff(w);
                    break;
                case OR:
                    for (i = w.sons; i != null ; i = i.next)
                    {
                        ANDs_below_ORs_in_wff(i);
                    }
                    merge_next_step_ANDs_and_ORs_in_wff(w);
                    break;
                case NOT:
                case ATOM:
                case TRU:
                case FAL:
                    break;
                default:
                    FFUtilities.Write("\nwon't get here: ands down, non logical %d\n\n",
                       w.connective);
                    Exit(1);
                    break;
            }

        }



        public  void collect_hitting_sets(WffNode ORlist, int index)

        {

            WffNode tmp1, tmp2, j;
            int i;

            if (ORlist == null)
            {
                tmp1 = new WffNode(AND);
                for (i = 0; i < index; i++)
                {
                    tmp2 = copy_Wff(lset[i]);
                    tmp2.next = tmp1.sons;
                    if (tmp1.sons != null)
                    {
                        tmp1.sons.prev = tmp2;
                    }
                    tmp1.sons = tmp2;
                }
                tmp1.next = lhitting_sets;
                if (lhitting_sets != null)
                {
                    lhitting_sets.prev = tmp1;
                }
                lhitting_sets = tmp1;
                return;
            }

            if (ORlist.connective != OR)
            {
                lset[index] = ORlist;
                collect_hitting_sets(ORlist.next, index + 1);
                return;
            }

            for (j = ORlist.sons; j != null; j = j.next)
            {
                lset[index] = j;
                collect_hitting_sets(ORlist.next, index + 1);
            }

        }



        public  void merge_next_step_ANDs_and_ORs_in_wff(WffNode w)

        {

            WffNode i, j, tmp;

            i = w.sons;
            while (i != null)
            {
                if (i.connective == w.connective)
                {
                    if (!(i.sons != null))
                    {
                        if (i.next != null)
                        {
                            i.next.prev = i.prev;
                        }
                        if (i.prev != null)
                        {
                            i.prev.next = i.next;
                        }
                        else
                        {
                            w.sons = i.next;
                        }
                        tmp = i;
                        i = i.next;
                        //free(tmp);
                        continue;
                    }
                    for (j = i.sons; j.next != null; j = j.next) ;
                    j.next = i.next;
                    if (i.next != null)
                    {
                        i.next.prev = j;
                    }
                    if (i.prev != null)
                    {
                        i.prev.next = i.sons;
                        i.sons.prev = i.prev;
                    }
                    else
                    {
                        w.sons = i.sons;
                    }
                    tmp = i;
                    i = i.next;
                    //free(tmp);
                    continue;
                }
                i = i.next;
            }

        }



        /*   switch ( w.connective ) { */
        /*   case ALL: */
        /*   case EX: */
        /*     break; */
        /*   case AND: */
        /*   case OR: */
        /*     for ( i = w.sons; i != null ; i = i.next ) { */
        /*     } */
        /*     break; */
        /*   case NOT: */
        /*     break; */
        /*   case ATOM: */
        /*   case TRU: */
        /*   case FAL: */
        /*     break; */
        /*   default: */
        /*     Utilities.Write("\nwon't get here: remove var, non logical %d\n\n", */
        /* 	   w.connective); */
        /*     System.Environment.Exit( 1 ); */
        /*   } */



    }
}
