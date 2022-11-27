
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
using static CPORLib.FFCS.Constants;
using static CPORLib.FFCS.FFUtilities;
using static CPORLib.FFCS.ConnectivityGraph;

namespace CPORLib.FFCS
{
    public class InstFinal
    {

        /* local globals for this part
         */

        static Array2D<int> lpos = new Array2D<int>(MAX_PREDICATES);// new int[MAX_PREDICATES];
        static Array2D<int> lneg = new Array2D<int>(MAX_PREDICATES);// new int[MAX_PREDICATES];
        static Array2D<int> luse = new Array2D<int>(MAX_PREDICATES);// new int[MAX_PREDICATES];
        static Array2D<int> lindex = new Array2D<int>(MAX_PREDICATES);// new int[MAX_PREDICATES];

        static int lp;
        static int[] largs = new int[MAX_VARS];







        public static void perform_reachability_analysis()

        {

            int size, i, j, k, adr, num;
            bool fixpoint;
            Facts f;
            NormOperator no;
            EasyTemplate t1, t2;
            NormEffect ne;
            Action tmp, a;
            bool[] had_hard_template;
            PseudoAction pa;
            PseudoActionEffect pae;

            FF.DP.gactions = null;
            FF.DP.gnum_actions = 0;

            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                size = 1;
                for (j = 0; j < FF.DP.garity[i]; j++)
                {
                    size *= FF.DP.gnum_constants;
                }

                lpos.Init(i,size);
                lneg.Init(i, size);
                luse.Init(i, size);
                lindex.Init(i, size);

                for (j = 0; j < size; j++)
                {
                    lpos[i, j] = 0;
                    lneg[i, j] = 1;/* all facts but initials are poss. negative */
                    luse[i, j] = 0;
                    lindex[i, j] = -1;
                }
            }

            had_hard_template = new bool[FF.DP.gnum_hard_templates];// (bool*)calloc(Main.DP.FF.Search.gnum_Hard_templates, sizeof(bool));
            for (i = 0; i < FF.DP.gnum_hard_templates; i++)
            {
                had_hard_template[i] = false;
            }

            /* mark initial facts as possibly positive, not poss. negative
             */
            for (i = 0; i < FF.DP.gnum_predicates; i++)
            {
                lp = i;
                for (j = 0; j < FF.DP.gnum_initial_predicate[i]; j++)
                {
                    for (k = 0; k < FF.DP.garity[i]; k++)
                    {
                        largs[k] = FF.DP.ginitial_predicate[i, j].args[k];
                    }
                    adr = fact_adress();
                    lpos[lp, adr] = 1;
                    lneg[lp, adr] = 0;
                }
            }

            /* compute fixpoint
             */
            fixpoint = false;
            while (!fixpoint)
            {
                fixpoint = true;

                /* assign next layer of easy templates to possibly positive fixpoint
                 */
                t1 = FF.DP.geasy_templates;
                while (t1 != null)
                {
                    no = t1.op;
                    for (i = 0; i < no.num_preconds; i++)
                    {
                        lp = no.preconds[i].predicate;
                        for (j = 0; j < FF.DP.garity[lp]; j++)
                        {
                            largs[j] = (no.preconds[i].args[j] >= 0) ?
                              no.preconds[i].args[j] : t1.inst_table[DECODE_VAR(no.preconds[i].args[j])];
                        }
                        if (lpos[lp, fact_adress()] == 0)
                        {
                            break;
                        }
                    }

                    if (i < no.num_preconds)
                    {
                        t1 = t1.next;
                        continue;
                    }

                    num = 0;
                    for (ne = no.effects; ne != null; ne = ne.next)
                    {
                        num++;
                        /* currently, simply ignore effect conditions and assume
                         * they will all be made true eventually.
                         */
                        for (i = 0; i < ne.num_adds; i++)
                        {
                            lp = ne.adds[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = (ne.adds[i].args[j] >= 0) ?
                                  ne.adds[i].args[j] : t1.inst_table[DECODE_VAR(ne.adds[i].args[j])];
                            }
                            adr = fact_adress();
                            if (lpos[lp, adr] == 0)
                            {
                                /* new relevant fact! (added non initial)
                                 */
                                lpos[lp, adr] = 1;
                                lneg[lp, adr] = 1;
                                luse[lp, adr] = 1;
                                if (FF.DP.gnum_relevant_facts == MAX_RELEVANT_FACTS)
                                {
                                    FFUtilities.Write("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
                                       MAX_RELEVANT_FACTS);
                                    Exit(1);
                                }
                                FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].predicate = lp;
                                for (j = 0; j < FF.DP.garity[lp]; j++)
                                {
                                    FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].args[j] = largs[j];
                                }
                                //Utilities.WriteLine("lindex[lp, adr] = " + lp + "," + adr + ", " + Main.DP.gnum_relevant_facts);
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                FF.DP.gnum_relevant_facts++;
                                fixpoint = false;
                            }
                        }
                    }

                    tmp = new Action(no, t1);
                    /*
                    tmp.norm_operator = no;
                    tmp.axiom = no.action_operator.axiom;
                    tmp.stratum = no.action_operator.stratum;
                    for (i = 0; i < no.num_vars; i++)
                    {
                        tmp.inst_table[i] = t1.inst_table[i];
                    }
                    tmp.name = no.action_operator.name;
                    tmp.num_name_vars = no.action_operator.number_of_real_params;
                    make_name_inst_table_from_NormOperator(tmp, no, t1);
                    */
                    tmp.next = FF.DP.gactions;
                    tmp.num_effects = num;
                    FF.DP.gactions = tmp;
                    FF.DP.gnum_actions++;

                    t2 = t1.next;
                    if (t1.next != null)
                    {
                        t1.next.prev = t1.prev;
                    }
                    if (t1.prev != null)
                    {
                        t1.prev.next = t1.next;
                    }
                    else
                    {
                        FF.DP.geasy_templates = t1.next;
                    }
                    //free1single1EasyTemplate(t1);
                    t1 = t2;
                }

                /* now assign all hard templates that have not been transformed
                 * to actions yet.
                 */
                for (i = 0; i < FF.DP.gnum_hard_templates; i++)
                {
                    if (had_hard_template[i])
                    {
                        continue;
                    }
                    pa = FF.DP.ghard_templates[i];

                    for (j = 0; j < pa.num_preconds; j++)
                    {
                        lp = pa.preconds[j].predicate;
                        for (k = 0; k < FF.DP.garity[lp]; k++)
                        {
                            largs[k] = pa.preconds[j].args[k];
                        }
                        if (lpos[lp, fact_adress()] == 0)
                        {
                            break;
                        }
                    }

                    if (j < pa.num_preconds)
                    {
                        continue;
                    }

                    for (pae = pa.effects; pae != null; pae = pae.next)
                    {
                        /* currently, simply ignore effect conditions and assume
                         * they will all be made true eventually.
                         */
                        for (j = 0; j < pae.num_adds; j++)
                        {
                            lp = pae.adds[j].predicate;
                            for (k = 0; k < FF.DP.garity[lp]; k++)
                            {
                                largs[k] = pae.adds[j].args[k];
                            }
                            adr = fact_adress();
                            if (lpos[lp, adr] == 0)
                            {
                                /* new relevant fact! (added non initial)
                                 */
                                lpos[lp, adr] = 1;
                                lneg[lp, adr] = 1;
                                luse[lp, adr] = 1;
                                if (FF.DP.gnum_relevant_facts == MAX_RELEVANT_FACTS)
                                {
                                    FFUtilities.Write("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
                                       MAX_RELEVANT_FACTS);
                                    Exit(1);
                                }
                                FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].predicate = lp;
                                for (k = 0; k < FF.DP.garity[lp]; k++)
                                {
                                    FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].args[k] = largs[k];
                                }
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                FF.DP.gnum_relevant_facts++;
                                fixpoint = false;
                            }
                        }
                    }

                    tmp = new Action(pa);
                    /*
                    tmp.pseudo_action = pa;
                    tmp.axiom = pa.action_operator.axiom;
                    tmp.stratum = pa.action_operator.stratum;
                    for (j = 0; j < pa.action_operator.num_vars; j++)
                    {
                        tmp.inst_table[j] = pa.inst_table[j];
                    }
                    tmp.name = pa.action_operator.name;
                    tmp.num_name_vars = pa.action_operator.number_of_real_params;
                    make_name_inst_table_from_PseudoAction(tmp, pa);
                    */
                    tmp.next = FF.DP.gactions;
                    tmp.num_effects = pa.num_effects;
                    FF.DP.gactions = tmp;
                    FF.DP.gnum_actions++;

                    had_hard_template[i] = true;
                }
            }

            //free(had_hard_template);

            FF.DP.gnum_pp_facts = FF.DP.gnum_initial + FF.DP.gnum_relevant_facts;

            if (gcmd_line.display_info == 118)
            {
                FFUtilities.Write("\nreachability analysys came up with:");

                FFUtilities.Write("\n\npossibly positive facts:");
                for (f = FF.DP.ginitial; f != null; f = f.next)
                {
                    FFUtilities.Write("\n");
                    print_Fact(f.fact);
                }
                for (i = 0; i < FF.DP.gnum_relevant_facts; i++)
                {
                    FFUtilities.Write("\n");
                    print_Fact((FF.DP.grelevant_facts[i]));
                }

                FFUtilities.Write("\n\nthis yields these %d action templates:" + FF.DP.gnum_actions);
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    FFUtilities.Write("\n\noperator: " + FF.DP.goperators[i].name);
                    for (a = FF.DP.gactions; a != null; a = a.next)
                    {
                        if ((a.norm_operator != null &&
                               a.norm_operator.action_operator != FF.DP.goperators[i]) ||
                             (a.pseudo_action != null &&
                               a.pseudo_action.action_operator != FF.DP.goperators[i]))
                        {
                            continue;
                        }
                        FFUtilities.Write("\ntemplate stratum %d: " + a.stratum);
                        if (a.axiom) 
                            FFUtilities.Write("(axiom) ");
                        for (j = 0; j < FF.DP.goperators[i].number_of_real_params; j++)
                        {
                            FFUtilities.Write(FF.DP.gconstants[a.name_inst_table[j]]);
                            if (j < FF.DP.goperators[i].num_vars - 1)
                            {
                                FFUtilities.Write(" ");
                            }
                        }
                    }
                }
                FFUtilities.Write("\n\n");
            }

        }



        static int fact_adress()
        {
            //Utilities.Write("fact_address: " + lp + ", " + Main.DP.garity[lp]);
            int r = 0, b = 1, i;

            for (i = FF.DP.garity[lp] - 1; i > -1; i--)
            {
                //Utilities.Write(", " + i + "=" + largs[i]);
                r += b * largs[i];
                b *= FF.DP.gnum_constants;
            }
            //Utilities.WriteLine();

            //if (lp == 1)
              //  Utilities.Write("*");

            return r;

        }


        


















        /***********************************************************
         * RELEVANCE ANALYSIS AND FINAL DOMAIN AND PROBLEM CLEANUP *
         ***********************************************************/









        /* counts effects for later allocation
         */
        static int lnum_effects;









        public static void collect_relevant_facts()

        {

            Action a;
            NormOperator no;
            NormEffect ne;
            int i, j, adr;
            PseudoAction pa;
            PseudoActionEffect pae;

            /* mark all deleted facts; such facts, that are also pos, are relevant.
             */
            for (a = FF.DP.gactions; a != null; a = a.next)
            {
                if (a.norm_operator != null)
                {
                    no = a.norm_operator;

                    for (ne = no.effects; ne != null; ne = ne.next)
                    {
                        for (i = 0; i < ne.num_dels; i++)
                        {
                            lp = ne.dels[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = (ne.dels[i].args[j] >= 0) ?
                                  ne.dels[i].args[j] : a.inst_table[DECODE_VAR(ne.dels[i].args[j])];
                            }
                            adr = fact_adress();

                            lneg[lp, adr] = 1;
                            if (lpos[lp, adr] != 0 &&
                                 luse[lp, adr] == 0)
                            {
                                luse[lp, adr] = 1;
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                if (FF.DP.gnum_relevant_facts == MAX_RELEVANT_FACTS)
                                {
                                    FFUtilities.Write("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
                                       MAX_RELEVANT_FACTS);
                                    Exit(1);
                                }
                                FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].predicate = lp;
                                for (j = 0; j < FF.DP.garity[lp]; j++)
                                {
                                    FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].args[j] = largs[j];
                                }
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                FF.DP.gnum_relevant_facts++;
                            }
                        }
                    }
                }
                else
                {
                    pa = a.pseudo_action;

                    for (pae = pa.effects; pae != null; pae = pae.next)
                    {
                        for (i = 0; i < pae.num_dels; i++)
                        {
                            lp = pae.dels[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = pae.dels[i].args[j];
                            }
                            adr = fact_adress();

                            lneg[lp, adr] = 1;
                            if (lpos[lp, adr] != 0 &&
                                 luse[lp, adr] == 0)
                            {
                                luse[lp, adr] = 1;
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                if (FF.DP.gnum_relevant_facts == MAX_RELEVANT_FACTS)
                                {
                                    FFUtilities.Write("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
                                       MAX_RELEVANT_FACTS);
                                    Exit(1);
                                }
                                FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].predicate = lp;
                                for (j = 0; j < FF.DP.garity[lp]; j++)
                                {
                                    FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].args[j] = largs[j];
                                }
                                lindex[lp, adr] = FF.DP.gnum_relevant_facts;
                                FF.DP.gnum_relevant_facts++;
                            }
                        }
                    }
                }
            }

            if (gcmd_line.display_info == 119)
            {
                FFUtilities.Write("\n\nfacts selected as relevant:\n\n");
                for (i = 0; i < FF.DP.gnum_relevant_facts; i++)
                {
                    FFUtilities.Write("\n%d: ", i);
                    print_Fact((FF.DP.grelevant_facts[i]));
                }
            }

            lnum_effects = 0;

            /* first make place for initial and goal states.
             * (one artificial fact miFF.Search.gHt still be added here)
             */
            //make1state(Main.DP.ggoal_state, Main.DP.gnum_relevant_facts + 1);
            FF.DP.ggoal_state = new FFState(FF.DP.gnum_relevant_facts + 1);
            FF.DP.ggoal_state.max_F = FF.DP.gnum_relevant_facts + 1;
            //make1state(Main.DP.ginitial_state, Main.DP.gnum_relevant_facts + 1);
            FF.DP.ginitial_state = new FFState(FF.DP.gnum_relevant_facts + 1);
            FF.DP.ginitial_state.max_F = FF.DP.gnum_relevant_facts + 1;

            create_final_goal_state();
            create_final_initial_state();
            create_final_actions();

            if (gcmd_line.display_info == 120)
            {
                FFUtilities.Write("\n\nfinal domain representation is:\n\n");
                for (i = 0; i < FF.DP.gnum_operators; i++)
                {
                    FFUtilities.Write("\n\n------------------operator %s-----------\n\n", FF.DP.goperators[i].name);
                    for (a = FF.DP.gactions; a != null; a = a.next)
                    {
                        if ((a.norm_operator == null &&
                               a.pseudo_action == null) ||
                             (a.norm_operator != null &&
                               (a.norm_operator.action_operator) != FF.DP.goperators[i]) ||
                             (a.pseudo_action != null &&
                               a.pseudo_action.action_operator != FF.DP.goperators[i]))
                        {
                            continue;
                        }
                        Output.print_Action(a);
                    }
                }
                FFUtilities.Write("\n\n--------------------GOAL REACHED ops-----------\n\n");
                for (a = FF.DP.gactions; a != null; a = a.next)
                {
                    if (a.norm_operator == null &&
                     a.pseudo_action == null)
                    {
                        Output.print_Action(a);
                    }
                }

                FFUtilities.Write("\n\nfinal initial state is:\n\n");
                for (i = 0; i < FF.DP.ginitial_state.num_F; i++)
                {
                    Output.print_ft_name(FF.DP.ginitial_state.F[i]);
                    FFUtilities.Write("\n");
                }
                FFUtilities.Write("\n\nfinal goal state is:\n\n");
                for (i = 0; i < FF.DP.ggoal_state.num_F; i++)
                {
                    print_ft_name(FF.DP.ggoal_state.F[i]);
                    FFUtilities.Write("\n");
                }
            }

        }



        static void create_final_goal_state()

        {

            WffNode w, ww;
            int m, i, adr;
            Action tmp;

            set_relevants_in_wff(FF.DP.ggoal);
            FF.IP.cleanup_wff(FF.DP.ggoal);
            if (FF.DP.ggoal.connective == TRU)
            {
                FFUtilities.Write("\nff: final: Main.DP.ggoal can be simplified to true. The empty plan solves it\n\n");
                Exit(1);
            }
            if (FF.DP.ggoal.connective == FAL)
            {
                FFUtilities.Write("\nff: goal can be simplified to false. No plan will solve it\n\n");
                Exit(1);
            }

            switch (FF.DP.ggoal.connective)
            {
                case OR:
                    if (FF.DP.gnum_relevant_facts == MAX_RELEVANT_FACTS)
                    {
                        FFUtilities.Write("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
                           MAX_RELEVANT_FACTS);
                        Exit(1);
                    }
                    FF.DP.grelevant_facts[FF.DP.gnum_relevant_facts].predicate = -3;
                    FF.DP.gnum_relevant_facts++;
                    for (w = FF.DP.ggoal.sons; w != null; w = w.next)
                    {
                        tmp = new Action();
                        if (w.connective == AND)
                        {
                            m = 0;
                            for (ww = w.sons; ww != null; ww = ww.next) m++;
                            tmp.preconds = new int[m];// new int[];//(m, sizeof(int));
                            tmp.num_preconds = 0;
                            for (ww = w.sons; ww != null; ww = ww.next)
                            {
                                lp = ww.fact.predicate;
                                for (i = 0; i < FF.DP.garity[lp]; i++)
                                {
                                    largs[i] = ww.fact.args[i];
                                }
                                adr = fact_adress();
                                tmp.preconds[tmp.num_preconds++] = lindex[lp, adr];
                            }
                        }
                        else
                        {
                            tmp.preconds = new int[1];// new int[];//(1, sizeof(int));
                            tmp.num_preconds = 1;
                            lp = w.fact.predicate;
                            for (i = 0; i < FF.DP.garity[lp]; i++)
                            {
                                largs[i] = w.fact.args[i];
                            }
                            adr = fact_adress();
                            tmp.preconds[0] = lindex[lp, adr];
                        }
                        tmp.effects = new ActionEffect[1];//  (ActionEffect*)calloc(1, sizeof(ActionEffect));
                        tmp.num_effects = 1;
                        tmp.effects[0].conditions = null;
                        tmp.effects[0].num_conditions = 0;
                        tmp.effects[0].dels = null;
                        tmp.effects[0].num_dels = 0;
                        tmp.effects[0].adds = new int[1];// new int[];//(1, sizeof(int));
                        tmp.effects[0].adds[0] = FF.DP.gnum_relevant_facts - 1;
                        tmp.effects[0].num_adds = 1;
                        tmp.next = FF.DP.gactions;
                        FF.DP.gactions = tmp;
                        FF.DP.gnum_actions++;
                        lnum_effects++;
                    }
                    FF.DP.ggoal_state.F[0] = FF.DP.gnum_relevant_facts - 1;
                    FF.DP.ggoal_state.num_F = 1;
                    break;
                case AND:
                    for (w = FF.DP.ggoal.sons; w != null; w = w.next)
                    {
                        lp = w.fact.predicate;
                        for (i = 0; i < FF.DP.garity[lp]; i++)
                        {
                            largs[i] = w.fact.args[i];
                        }
                        adr = fact_adress();
                        FF.DP.ggoal_state.F[FF.DP.ggoal_state.num_F++] = lindex[lp, adr];
                    }
                    break;
                case ATOM:
                    FF.DP.ggoal_state.num_F = 1;
                    lp = FF.DP.ggoal.fact.predicate;
                    for (i = 0; i < FF.DP.garity[lp]; i++)
                    {
                        largs[i] = FF.DP.ggoal.fact.args[i];
                    }
                    adr = fact_adress();
                    FF.DP.ggoal_state.F[0] = lindex[lp, adr];
                    break;
                default:
                    FFUtilities.Write("\n\nwon't get here: non ATOM,AND,OR in fully simplified goal\n\n");
                    Exit(1);
                    break;
            }

        }



        static void set_relevants_in_wff(WffNode w)

        {

            WffNode i;
            int j, adr;

            switch (w.connective)
            {
                case AND:
                case OR:
                    for (i = w.sons; i != null; i = i.next)
                    {
                        set_relevants_in_wff(i);
                    }
                    break;
                case ATOM:
                    /* no equalities, as fully instantiated
                     */
                    lp = w.fact.predicate;
                    for (j = 0; j < FF.DP.garity[lp]; j++)
                    {
                        largs[j] = w.fact.args[j];
                    }
                    adr = fact_adress();

                    if (lneg[lp, adr] == 0)
                    {
                        w.connective = TRU;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
                    if (lpos[lp, adr] == 0)
                    {
                        w.connective = FAL;
                        //free(w.fact);
                        w.fact = null;
                        break;
                    }
                    break;
                default:
                    FFUtilities.Write("\n\nwon't get here: non NOT,OR,AND in goal set relevants\n\n");
                    Exit(1);
                    break;
            }

        }



        static void create_final_initial_state()

        {

            Facts f;
            int i, adr;

            for (f = FF.DP.ginitial; f != null; f = f.next)
            {
                lp = f.fact.predicate;
                for (i = 0; i < FF.DP.garity[lp]; i++)
                {
                    largs[i] = f.fact.args[i];
                }
                adr = fact_adress();

                if (lneg[lp, adr] == 0)
                {/* non deleted ini */
                    continue;
                }

                FF.DP.ginitial_state.F[FF.DP.ginitial_state.num_F++] = lindex[lp, adr];
            }

        }



        static void create_final_actions()

        {

            Action a, p, t;
            NormOperator no;
            NormEffect ne;
            int i, j, adr;
            PseudoAction pa;
            PseudoActionEffect pae;
            bool has;

            a = FF.DP.gactions; p = null;
            while (a != null)
            {
                if (a.norm_operator != null)
                {
                    /* action comes from an easy template NormOp
                     */
                    no = a.norm_operator;

                    //Utilities.WriteLine("a.norm_operator: " + a.norm_operator);

                    if (no.num_preconds > 0)
                    {
                        a.preconds = new int[no.num_preconds];// new int[];//(, sizeof(int));
                    }
                    a.num_preconds = 0;
                    for (i = 0; i < no.num_preconds; i++)
                    {
                        lp = no.preconds[i].predicate;
                        //Utilities.WriteLine("no.preconds[i].predicate: " + no.preconds[i].predicate);
                        for (j = 0; j < FF.DP.garity[lp]; j++)
                        {
                            largs[j] = (no.preconds[i].args[j] >= 0) ?
                              no.preconds[i].args[j] : a.inst_table[DECODE_VAR(no.preconds[i].args[j])];
                            //Utilities.WriteLine(j + ") largs[j] = " + largs[j]);
                        }
                        adr = fact_adress();
                        //Utilities.WriteLine("adr: " + adr);

                        /* preconds are lpos in all cases due to reachability analysis
                         */
                        if (lneg[lp, adr] == 0)
                        {
                            continue;
                        }
                

                        a.preconds[a.num_preconds++] = lindex[lp, adr];
                    }

                    if (a.num_effects > 0)
                    {
                        a.effects = new ActionEffect[a.num_effects];// (ActionEffect*)calloc(, sizeof(ActionEffect));
                        for(i = 0 ; i < a.num_effects; i++)
                            a.effects[i] = new ActionEffect();
                    }
                    a.num_effects = 0;
                    has = false;
                    for (ne = no.effects; ne != null; ne = ne.next)
                    {
                        if (ne.num_conditions > 0)
                        {
                            a.effects[a.num_effects].conditions = new int[ne.num_conditions];

                        }
                        a.effects[a.num_effects].num_conditions = 0;

                        for (i = 0; i < ne.num_conditions; i++)
                        {
                            lp = ne.conditions[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = (ne.conditions[i].args[j] >= 0) ?
                                  ne.conditions[i].args[j] : a.inst_table[DECODE_VAR(ne.conditions[i].args[j])];
                            }
                            adr = fact_adress();
                            if (lpos[lp, adr] == 0)
                            {/* condition not reachable: skip effect */
                                break;
                            }
                            if (lneg[lp, adr] == 0)
                            {/* condition always true: skip it */
                                continue;
                            }
                            a.effects[a.num_effects].conditions[a.effects[a.num_effects].num_conditions++] =
                              lindex[lp, adr];
                        }

                        if (i < ne.num_conditions)
                        {/* found unreachable condition: free condition space */
                            //free(a.effects[a.num_effects].conditions);
                            continue;
                        }

                        /* now create the add and del effects.
                         */
                        if (ne.num_adds > 0)
                        {
                            a.effects[a.num_effects].adds = new int[ne.num_adds]; // new int[];//(, sizeof(int));
                        }
                        a.effects[a.num_effects].num_adds = 0;
                        for (i = 0; i < ne.num_adds; i++)
                        {
                            lp = ne.adds[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = (ne.adds[i].args[j] >= 0) ?
                                  ne.adds[i].args[j] : a.inst_table[DECODE_VAR(ne.adds[i].args[j])];
                            }
                            adr = fact_adress();

                            if (lneg[lp, adr] == 0)
                            {/* effect always true: skip it */
                                continue;
                            }
                            has = true;
                            a.effects[a.num_effects].adds[a.effects[a.num_effects].num_adds++] = lindex[lp, adr];
                        }

                        if (ne.num_dels > 0)
                        {
                            a.effects[a.num_effects].dels = new int[ne.num_dels];// new int[];//(, sizeof(int));
                        }
                        a.effects[a.num_effects].num_dels = 0;
                        for (i = 0; i < ne.num_dels; i++)
                        {
                            lp = ne.dels[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = (ne.dels[i].args[j] >= 0) ?
                                    ne.dels[i].args[j] : a.inst_table[DECODE_VAR(ne.dels[i].args[j])];
                            }
                            adr = fact_adress();

                            if (lpos[lp, adr] == 0)
                            {/* effect always false: skip it */
                                continue;
                            }
                            has = true;
                            a.effects[a.num_effects].dels[a.effects[a.num_effects].num_dels++] = lindex[lp, adr];
                        }
                        if (i < ne.num_dels) 
                            break;

                        /* this effect is OK. go to next one in NormOp.
                         */
                        a.num_effects++;
                        lnum_effects++;
                    }
                    if (!has || ne != null)
                    {
                        FF.DP.gnum_actions--;
                        /* we get here if one effect was faulty
                         */
                        if (p != null)
                        {
                            p.next = a.next;
                            t = a;
                            a = a.next;
                            //free1single1Action(t);
                        }
                        else
                        {
                            FF.DP.gactions = a.next;
                            t = a;
                            a = a.next;
                            //free1single1Action(t);
                        }
                    }
                    else
                    {
                        p = a;
                        a = a.next;
                    }
                    continue;
                }
                if (a.pseudo_action != null)
                {
                    /* action is result of a PseudoAction
                     */
                    pa = a.pseudo_action;

                    if (pa.num_preconds > 0)
                    {
                        a.preconds = new int[pa.num_preconds];// new int[];//(, sizeof(int));
                    }
                    a.num_preconds = 0;
                    for (i = 0; i < pa.num_preconds; i++)
                    {
                        lp = pa.preconds[i].predicate;
                        for (j = 0; j < FF.DP.garity[lp]; j++)
                        {
                            largs[j] = pa.preconds[i].args[j];
                        }
                        adr = fact_adress();

                        /* preconds are lpos in all cases due to reachability analysis
                         */
                        if (lneg[lp, adr] == 0)
                        {
                            continue;
                        }

                        a.preconds[a.num_preconds++] = lindex[lp, adr];
                    }

                    if (a.num_effects > 0)
                    {
                        a.effects = new ActionEffect[a.num_effects];// (ActionEffect*)calloc(, sizeof(ActionEffect));
                    }
                    a.num_effects = 0;
                    has = false;
                    for (pae = pa.effects; pae != null; pae = pae.next)
                    {
                        if (pae.num_conditions > 0)
                        {
                            a.effects[a.num_effects].conditions = new int[pae.num_conditions];

                        }
                        a.effects[a.num_effects].num_conditions = 0;

                        for (i = 0; i < pae.num_conditions; i++)
                        {
                            lp = pae.conditions[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = pae.conditions[i].args[j];
                            }
                            adr = fact_adress();

                            if (lpos[lp, adr] == 0)
                            {/* condition not reachable: skip effect */
                                break;
                            }
                            if (lneg[lp, adr] == 0)
                            {/* condition always true: skip it */
                                continue;
                            }

                            a.effects[a.num_effects].conditions[a.effects[a.num_effects].num_conditions++] =
                              lindex[lp, adr];
                        }

                        if (i < pae.num_conditions)
                        {/* found unreachable condition: free condition space */
                            //free(a.effects[a.num_effects].conditions);
                            continue;
                        }

                        /* now create the add and del effects.
                         */
                        if (pae.num_adds > 0)
                        {
                            a.effects[a.num_effects].adds = new int[pae.num_adds];// new int[];//(, sizeof(int));
                        }
                        a.effects[a.num_effects].num_adds = 0;
                        for (i = 0; i < pae.num_adds; i++)
                        {
                            lp = pae.adds[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = pae.adds[i].args[j];
                            }
                            adr = fact_adress();

                            if (lneg[lp, adr] == 0)
                            {/* effect always true: skip it */
                                continue;
                            }
                            has = true;
                            a.effects[a.num_effects].adds[a.effects[a.num_effects].num_adds++] = lindex[lp, adr];
                        }

                        if (pae.num_dels > 0)
                        {
                            a.effects[a.num_effects].dels = new int[pae.num_dels];
                        }
                        a.effects[a.num_effects].num_dels = 0;
                        for (i = 0; i < pae.num_dels; i++)
                        {
                            lp = pae.dels[i].predicate;
                            for (j = 0; j < FF.DP.garity[lp]; j++)
                            {
                                largs[j] = pae.dels[i].args[j];
                            }
                            adr = fact_adress();

                            if (lpos[lp, adr] == 0)
                            {/* effect always false: skip it */
                                continue;
                            }
                            has = true;
                            a.effects[a.num_effects].dels[a.effects[a.num_effects].num_dels++] = lindex[lp, adr];
                        }
                        if (i < pae.num_dels) break;

                        /* this effect is OK. go to next one in PseudoAction.
                         */
                        a.num_effects++;
                        lnum_effects++;
                    }
                    if (!has || pae != null)
                    {
                        FF.DP.gnum_actions--;
                        /* we get here if one effect was faulty
                         */
                        if (p != null)
                        {
                            p.next = a.next;
                            t = a;
                            a = a.next;
                            //free1single1Action(t);
                        }
                        else
                        {
                            FF.DP.gactions = a.next;
                            t = a;
                            a = a.next;
                            //free1single1Action(t);
                        }
                    }
                    else
                    {
                        p = a;
                        a = a.next;
                    }
                    continue;
                }/* end of if clause for PseudoAction */
                /* if action was neither normop, nor pseudo action determined,
                 * then it is an artificial action due to disjunctive goal
                 * conditions.
                 *
                 * these are already in final form.
                 */
                p = a;
                a = a.next;
            }/* endfor all actions ! */

        }















        /**************************************************
         * CONNECTIVITY GRAPH. ULTRA CLEAN REPRESENTATION *
         **************************************************/













        public static void build_connectivity_graph()

        {

            int i, j, k, l, n_op, n_ef, na, nd, ef, ef_, l_, m;
            Action a;
            int[] same_effects;
            int sn;
            bool[] had_effects;
            ActionEffect e, e1, e2;



            FF.CF.gnum_ft_conn = FF.DP.gnum_relevant_facts;
            FF.CF.gnum_op_conn = FF.DP.gnum_actions;
            FF.CF.gft_conn = new InitializedArray<FtConn>(FF.CF.gnum_ft_conn);// (FtConn* ) calloc(, sizeof(FtConn ) );
            FF.CF.gop_conn = new InitializedArray<OpConn>(FF.CF.gnum_op_conn);// (OpConn* ) calloc(, sizeof(OpConn ) );
            FF.CF.gef_conn = new InitializedArray<EfConn>(lnum_effects);// (EfConn* ) calloc(, sizeof(EfConn ) );
            FF.CF.gnum_ef_conn = 0;

            same_effects = new int[lnum_effects];// (int* ) calloc(, sizeof(int ) );
            had_effects = new bool[lnum_effects];// (bool* ) calloc(, sizeof(bool ) );

            for (i = 0; i < FF.CF.gnum_ft_conn; i++)
            {
                


                FF.CF.gft_conn[i].num_PC = 0;
                FF.CF.gft_conn[i].num_A = 0;
                FF.CF.gft_conn[i].num_D = 0;

                FF.CF.gft_conn[i].num_axPC = 0;
                FF.CF.gft_conn[i].num_naxPC = 0;

                FF.CF.gft_conn[i].axiom_add = false;
                FF.CF.gft_conn[i].axiom_del = false;

                FF.CF.gft_conn[i].rand = random(BIG_INT);
            }
            FF.Planning.gaxdels = new int[FF.CF.gnum_ft_conn];//(, sizeof(int ) );
            FF.Planning.gnum_axdels = 0;


            for (i = 0; i < FF.CF.gnum_op_conn; i++)
            {
                FF.CF.gop_conn[i].num_E = 0;
            }

            for (i = 0; i < lnum_effects; i++)
            {
                FF.CF.gef_conn[i].num_PC = 0;
                FF.CF.gef_conn[i].num_A = 0;
                FF.CF.gef_conn[i].num_D = 0;
                FF.CF.gef_conn[i].num_I = 0;

                FF.CF.gef_conn[i].removed = false;
            }


            n_op = 0;
            n_ef = 0;
            for (a = FF.DP.gactions; a != null; a = a.next)
            {

                FF.CF.gop_conn[n_op].action = a;
                FF.CF.gop_conn[n_op].axiom = a.axiom;
                FF.CF.gop_conn[n_op].stratum = a.stratum;

                FF.CF.gop_conn[n_op].E = new int[a.num_effects];//(, sizeof(int));
                for (i = 0; i < a.num_effects; i++)
                {
                    had_effects[i] = false;
                }
                for (i = 0; i < a.num_effects; i++)
                {
                    if (had_effects[i])
                    {
                        continue;
                    }
                    had_effects[i] = true;
                    e = (a.effects[i]);
                    FF.CF.gop_conn[n_op].E[FF.CF.gop_conn[n_op].num_E++] = n_ef;
                    FF.CF.gef_conn[n_ef].op = n_op;

                    FF.CF.gef_conn[n_ef].PC = new Array<int>(e.num_conditions + a.num_preconds);

                    for (j = 0; j < a.num_preconds; j++)
                    {
                        for (k = 0; k < FF.CF.gef_conn[n_ef].num_PC; k++)
                        {
                            if (FF.CF.gef_conn[n_ef].PC[k] == a.preconds[j]) 
                                break;
                        }
                        if (k < FF.CF.gef_conn[n_ef].num_PC) 
                            continue;
                        FF.CF.gef_conn[n_ef].PC[FF.CF.gef_conn[n_ef].num_PC++] = a.preconds[j];
                    }
                    for (j = 0; j < e.num_conditions; j++)
                    {
                        for (k = 0; k < FF.CF.gef_conn[n_ef].num_PC; k++)
                        {
                            if (FF.CF.gef_conn[n_ef].PC[k] == e.conditions[j]) break;
                        }
                        if (k < FF.CF.gef_conn[n_ef].num_PC) continue;
                        FF.CF.gef_conn[n_ef].PC[FF.CF.gef_conn[n_ef].num_PC++] = e.conditions[j];
                    }

                    sn = 0;
                    for (j = i + 1; j < a.num_effects; j++)
                    {
                        if (had_effects[j])
                        {
                            continue;
                        }
                        e1 = (a.effects[j]);
                        /* check conditions
                         */
                        for (k = 0; k < e1.num_conditions; k++)
                        {
                            for (l = 0; l < e.num_conditions; l++)
                            {
                                if (e1.conditions[k] == e.conditions[l])
                                {
                                    break;
                                }
                            }
                            if (l == e.num_conditions)
                            {
                                break;
                            }
                        }
                        if (k < e1.num_conditions)
                        {
                            continue;
                        }
                        if (e.num_conditions == e1.num_conditions)
                        {
                            same_effects[sn++] = j;
                        }
                    }

                    na = e.num_adds;
                    nd = e.num_dels;
                    for (j = 0; j < sn; j++)
                    {
                        na += a.effects[same_effects[j]].num_adds;
                        nd += a.effects[same_effects[j]].num_dels;
                    }
                    FF.CF.gef_conn[n_ef].A = new int[na];//(na, sizeof(int));
                    FF.CF.gef_conn[n_ef].D = new int[nd];//(, sizeof(int));
                    for (j = 0; j < e.num_adds; j++)
                    {
                        for (k = 0; k < FF.CF.gef_conn[n_ef].num_A; k++)
                        {
                            if (FF.CF.gef_conn[n_ef].A[k] == e.adds[j]) 
                                break;
                        }
                        if (k < FF.CF.gef_conn[n_ef].num_A) 
                            continue;
                        /* exclude already true adds
                         */
                        for (k = 0; k < FF.CF.gef_conn[n_ef].num_PC; k++)
                        {
                            if (FF.CF.gef_conn[n_ef].PC[k] == e.adds[j]) 
                                break;
                        }
                        if (k < FF.CF.gef_conn[n_ef].num_PC) 
                            continue;
                        FF.CF.gef_conn[n_ef].A[FF.CF.gef_conn[n_ef].num_A++] = e.adds[j];
                    }
                    for (j = 0; j < e.num_dels; j++)
                    {
                        for (k = 0; k < FF.CF.gef_conn[n_ef].num_D; k++)
                        {
                            if (FF.CF.gef_conn[n_ef].D[k] == e.dels[j]) break;
                        }
                        if (k < FF.CF.gef_conn[n_ef].num_D) continue;
                        /* exclude re-added dels; check against *all*
                         * adds to be integrated.
                         */
                        for (k = 0; k < e.num_adds; k++)
                        {
                            if (e.adds[k] == e.dels[j]) break;
                        }
                        if (k < e.num_adds) continue;
                        for (l = 0; l < sn; l++)
                        {
                            e1 = (a.effects[same_effects[l]]);
                            for (k = 0; k < e1.num_adds; k++)
                            {
                                if (e1.adds[k] == e.dels[j]) break;
                            }
                            if (k < e1.num_adds) break;
                        }
                        if (l < sn) continue;
                        FF.CF.gef_conn[n_ef].D[FF.CF.gef_conn[n_ef].num_D++] = e.dels[j];
                    }
                    for (j = 0; j < sn; j++)
                    {
                        e1 = (a.effects[same_effects[j]]);
                        for (l = 0; l < e1.num_adds; l++)
                        {
                            for (k = 0; k < FF.CF.gef_conn[n_ef].num_A; k++)
                            {
                                if (FF.CF.gef_conn[n_ef].A[k] == e1.adds[l]) break;
                            }
                            if (k < FF.CF.gef_conn[n_ef].num_A) continue;
                            for (k = 0; k < FF.CF.gef_conn[n_ef].num_PC; k++)
                            {
                                if (FF.CF.gef_conn[n_ef].PC[k] == e1.adds[l]) break;
                            }
                            if (k < FF.CF.gef_conn[n_ef].num_PC) continue;
                            FF.CF.gef_conn[n_ef].A[FF.CF.gef_conn[n_ef].num_A++] = e1.adds[l];
                        }
                        for (l = 0; l < e1.num_dels; l++)
                        {
                            for (k = 0; k < FF.CF.gef_conn[n_ef].num_D; k++)
                            {
                                if (FF.CF.gef_conn[n_ef].D[k] == e1.dels[l]) break;
                            }
                            if (k < FF.CF.gef_conn[n_ef].num_D) continue;
                            /* exclude re-added dels; check against *all*
                             * adds to be integrated.
                             */
                            for (k = 0; k < e.num_adds; k++)
                            {
                                if (e.adds[k] == e1.dels[l]) break;
                            }
                            if (k < e.num_adds) continue;
                            for (l_ = 0; l_ < sn; l_++)
                            {
                                e2 = (a.effects[same_effects[l_]]);
                                for (k = 0; k < e2.num_adds; k++)
                                {
                                    if (e2.adds[k] == e1.dels[l]) break;
                                }
                                if (k < e2.num_adds) break;
                            }
                            if (l_ < sn) continue;
                            FF.CF.gef_conn[n_ef].D[FF.CF.gef_conn[n_ef].num_D++] = e1.dels[l];
                        }
                    }/* same cond effects */
                    for (j = 0; j < sn; j++)
                    {
                        had_effects[same_effects[j]] = true;
                    }

                    n_ef++;
                    FF.CF.gnum_ef_conn++;
                }/* ende all a.effects */

                if (FF.CF.gop_conn[n_op].num_E >= 1)
                {
                    /* CHECK EMPTY EFFECTS!
                     *
                     * two step process --- first, remove all effects that are entirely empty.
                     *                      second, check if all remaining effects are illegal
                     *                      or only delete:
                     *                      in that case, the op will never do any good so we 
                     *                      remove all its effects.
                     */
                    i = 0;
                    while (i < FF.CF.gop_conn[n_op].num_E)
                    {
                        if (FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[i]].num_A != 0 ||
                             FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[i]].num_D != 0)
                        {
                            i++;
                            continue;
                        }
                        /* we keep it in the Main.CF.gef_conn (seems easier), 
                         * but mark it as removed, which will exclude it from everything.
                         */
                        FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[i]].removed = true;
                        for (j = i; j < FF.CF.gop_conn[n_op].num_E - 1; j++)
                        {
                            FF.CF.gop_conn[n_op].E[j] = FF.CF.gop_conn[n_op].E[j + 1];
                        }
                        FF.CF.gop_conn[n_op].num_E--;
                    }

                    m = 0;
                    for (i = 0; i < FF.CF.gop_conn[n_op].num_E; i++)
                    {
                        if (FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[i]].num_A == 0)
                        {
                            m++;
                        }
                    }
                    if (m == FF.CF.gop_conn[n_op].num_E)
                    {
                        /* all remaining effects solely-deleters.
                         */
                        for (i = 0; i < FF.CF.gop_conn[n_op].num_E; i++)
                        {
                            FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[i]].removed = true;
                        }
                        FF.CF.gop_conn[n_op].num_E = 0;
                    }
                }

                /* setup implied effects info
                 */
                if (FF.CF.gop_conn[n_op].num_E > 1)
                {
                    for (i = 0; i < FF.CF.gop_conn[n_op].num_E; i++)
                    {
                        ef = FF.CF.gop_conn[n_op].E[i];
                        FF.CF.gef_conn[ef].I = new int[FF.CF.gop_conn[n_op].num_E];//(, sizeof(int));
                        FF.CF.gef_conn[ef].num_I = 0;
                    }
                    for (i = 0; i < FF.CF.gop_conn[n_op].num_E - 1; i++)
                    {
                        ef = FF.CF.gop_conn[n_op].E[i];
                        for (j = i + 1; j < FF.CF.gop_conn[n_op].num_E; j++)
                        {
                            ef_ = FF.CF.gop_conn[n_op].E[j];
                            /* ef ==> ef_ ? */
                            for (k = 0; k < FF.CF.gef_conn[ef_].num_PC; k++)
                            {
                                for (l = 0; l < FF.CF.gef_conn[ef].num_PC; l++)
                                {
                                    if (FF.CF.gef_conn[ef].PC[l] == FF.CF.gef_conn[ef_].PC[k]) break;
                                }
                                if (l == FF.CF.gef_conn[ef].num_PC) break;
                            }
                            if (k == FF.CF.gef_conn[ef_].num_PC)
                            {
                                FF.CF.gef_conn[ef].I[FF.CF.gef_conn[ef].num_I++] = ef_;
                            }
                            /* j ==> i ? */
                            for (k = 0; k < FF.CF.gef_conn[ef].num_PC; k++)
                            {
                                for (l = 0; l < FF.CF.gef_conn[ef_].num_PC; l++)
                                {
                                    if (FF.CF.gef_conn[ef_].PC[l] == FF.CF.gef_conn[ef].PC[k]) break;
                                }
                                if (l == FF.CF.gef_conn[ef_].num_PC) break;
                            }
                            if (k == FF.CF.gef_conn[ef].num_PC)
                            {
                                FF.CF.gef_conn[ef_].I[FF.CF.gef_conn[ef_].num_I++] = ef;
                            }
                        }
                    }
                }

                if (FF.CF.gop_conn[n_op].stratum == 0)
                {
                    FF.CF.gef_conn[FF.CF.gop_conn[n_op].E[0]].num_D = 0;
                }

                /* first sweep: only count the space we need for the fact arrays !
                 */
                if (FF.CF.gop_conn[n_op].num_E > 0)
                {
                    for (i = 0; i < FF.CF.gop_conn[n_op].num_E; i++)
                    {
                        ef = FF.CF.gop_conn[n_op].E[i];
                        if (FF.CF.gef_conn[ef].removed) 
                            continue;
                        for (j = 0; j < FF.CF.gef_conn[ef].num_PC; j++)
                        {
                            //Utilities.WriteLine("ef=" + ef + " n_op= " + n_op + " Main.CF.gef_conn[ef].PC[j] = " + Main.CF.gef_conn[ef].PC[j]);

                            FF.CF.gft_conn[FF.CF.gef_conn[ef].PC[j]].num_PC++;
                            if (FF.CF.gop_conn[n_op].axiom)
                            {
                                FF.CF.gft_conn[FF.CF.gef_conn[ef].PC[j]].num_axPC++;
                            }
                            else
                            {
                                FF.CF.gft_conn[FF.CF.gef_conn[ef].PC[j]].num_naxPC++;
                            }
                        }
                        for (j = 0; j < FF.CF.gef_conn[ef].num_A; j++)
                        {
                            FF.CF.gft_conn[FF.CF.gef_conn[ef].A[j]].num_A++;
                            if (FF.CF.gop_conn[n_op].axiom)
                            {
                                FF.CF.gft_conn[FF.CF.gef_conn[ef].A[j]].axiom_add = true;
                            }
                        }
                        for (j = 0; j < FF.CF.gef_conn[ef].num_D; j++)
                        {
                            FF.CF.gft_conn[FF.CF.gef_conn[ef].D[j]].num_D++;
                            if (FF.CF.gop_conn[n_op].axiom)
                            {
                                FF.CF.gft_conn[FF.CF.gef_conn[ef].D[j]].axiom_del = true;
                            }
                        }
                    }
                }

                n_op++;
            }

            for (i = 0; i < FF.CF.gnum_ft_conn; i++)
            {
                if (FF.CF.gft_conn[i].num_PC > 0)
                {
                    FF.CF.gft_conn[i].PC = new int[FF.CF.gft_conn[i].num_PC];//(, sizeof(int));
                }
                FF.CF.gft_conn[i].num_PC = 0;
                if (FF.CF.gft_conn[i].num_axPC > 0)
                {
                    FF.CF.gft_conn[i].axPC = new int[FF.CF.gft_conn[i].num_axPC];//(, sizeof(int));
                }
                FF.CF.gft_conn[i].num_axPC = 0;
                if (FF.CF.gft_conn[i].num_naxPC > 0)
                {
                    FF.CF.gft_conn[i].naxPC = new int[FF.CF.gft_conn[i].num_naxPC];//(, sizeof(int));
                }
                FF.CF.gft_conn[i].num_naxPC = 0;
                if (FF.CF.gft_conn[i].num_A > 0)
                {
                    FF.CF.gft_conn[i].A = new int[FF.CF.gft_conn[i].num_A];//(, sizeof(int));
                }
                FF.CF.gft_conn[i].num_A = 0;
                if (FF.CF.gft_conn[i].num_D > 0)
                {
                    FF.CF.gft_conn[i].D = new int[FF.CF.gft_conn[i].num_D];//(, sizeof(int));
                }
                FF.CF.gft_conn[i].num_D = 0;

                FF.CF.gft_conn[i].is_global_goal = false;
                if (FF.CF.gft_conn[i].axiom_del)
                {
                    FF.Planning.gaxdels[FF.Planning.gnum_axdels++] = i;
                }
            }
            for (i = 0; i < FF.DP.ggoal_state.num_F; i++)
            {
                FF.CF.gft_conn[FF.DP.ggoal_state.F[i]].is_global_goal = true;
            }
            if (gcmd_line.debug >= 1)
            {
                FFUtilities.Write("\n\n----------------------------------------------axdels: ");
                for (i = 0; i < FF.Planning.gnum_axdels; i++)
                {
                    FFUtilities.Write("\n");
                    print_ft_name(FF.Planning.gaxdels[i]);
                }
            }

            for (i = 0; i < FF.CF.gnum_ef_conn; i++)
            {
                if (FF.CF.gef_conn[i].removed) continue;
                for (j = 0; j < FF.CF.gef_conn[i].num_PC; j++)
                {
                    FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].PC[FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].num_PC++] = i;
                }
                if (FF.CF.gop_conn[FF.CF.gef_conn[i].op].axiom)
                {
                    for (j = 0; j < FF.CF.gef_conn[i].num_PC; j++)
                    {
                        FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].axPC[FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].num_axPC++] = i;
                    }
                }
                else
                {
                    for (j = 0; j < FF.CF.gef_conn[i].num_PC; j++)
                    {
                        FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].naxPC[FF.CF.gft_conn[FF.CF.gef_conn[i].PC[j]].num_naxPC++] = i;
                    }
                }
                for (j = 0; j < FF.CF.gef_conn[i].num_A; j++)
                {
                    FF.CF.gft_conn[FF.CF.gef_conn[i].A[j]].A[FF.CF.gft_conn[FF.CF.gef_conn[i].A[j]].num_A++] = i;
                }
                for (j = 0; j < FF.CF.gef_conn[i].num_D; j++)
                {
                    FF.CF.gft_conn[FF.CF.gef_conn[i].D[j]].D[FF.CF.gft_conn[FF.CF.gef_conn[i].D[j]].num_D++] = i;
                }
            }

            //free(same1effects);
            //free(had_effects);



            if (gcmd_line.display_info == 121)
            {
                FFUtilities.Write("\n\ncreated connectivity graph as follows:");

                FFUtilities.Write("\n\n------------------OP ARRAY %d:-----------------------",
                   FF.CF.gnum_op_conn);
                for (i = 0; i < FF.CF.gnum_op_conn; i++)
                {
                    FFUtilities.Write("\n\nOP %d, stratum %d: ", i, FF.CF.gop_conn[i].stratum);
                    if (FF.CF.gop_conn[i].axiom) FFUtilities.Write("(axiom) ");
                    Output.print_op_name(i);
                    FFUtilities.Write("\n----------EFFS %d:", FF.CF.gop_conn[i].num_E);
                    for (j = 0; j < FF.CF.gop_conn[i].num_E; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gop_conn[i].E[j]);
                    }
                }

                FFUtilities.Write("\n\n-------------------EFFECT ARRAY:----------------------");

                for (i = 0; i < FF.CF.gnum_ef_conn; i++)
                {
                    FFUtilities.Write("\n\neffect %d of op %d: ", i, FF.CF.gef_conn[i].op);
                    print_op_name(FF.CF.gef_conn[i].op);
                    if (FF.CF.gef_conn[i].removed)
                    {
                        FFUtilities.Write(" --- REMOVED ");
                        continue;
                    }
                    FFUtilities.Write("\n----------PCS:");
                    for (j = 0; j < FF.CF.gef_conn[i].num_PC; j++)
                    {
                        FFUtilities.Write("\n");
                        print_ft_name(FF.CF.gef_conn[i].PC[j]);
                    }
                    FFUtilities.Write("\n----------ADDS:");
                    for (j = 0; j < FF.CF.gef_conn[i].num_A; j++)
                    {
                        FFUtilities.Write("\n");
                        print_ft_name(FF.CF.gef_conn[i].A[j]);
                    }
                    FFUtilities.Write("\n----------DELS:");
                    for (j = 0; j < FF.CF.gef_conn[i].num_D; j++)
                    {
                        FFUtilities.Write("\n");
                        print_ft_name(FF.CF.gef_conn[i].D[j]);
                    }
                    FFUtilities.Write("\n----------IMPLIEDS:");
                    for (j = 0; j < FF.CF.gef_conn[i].num_I; j++)
                    {
                        FFUtilities.Write("\nimplied effect %d of op %d: ",
                               FF.CF.gef_conn[i].I[j], FF.CF.gef_conn[FF.CF.gef_conn[i].I[j]].op);
                        print_op_name(FF.CF.gef_conn[FF.CF.gef_conn[i].I[j]].op);
                    }
                }

                FFUtilities.Write("\n\n----------------------FT ARRAY:-----------------------------");
                for (i = 0; i < FF.CF.gnum_ft_conn; i++)
                {
                    FFUtilities.Write("\n\nFT: ");
                    print_ft_name(i);
                    FFUtilities.Write(" rand: %d", FF.CF.gft_conn[i].rand);
                    FFUtilities.Write(" --------- AXIOM ADD %d, AXIOM DEL %d",
                       FF.CF.gft_conn[i].axiom_add,
                       FF.CF.gft_conn[i].axiom_del);
                    FFUtilities.Write("\n----------PRE COND OF:");
                    for (j = 0; j < FF.CF.gft_conn[i].num_PC; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gft_conn[i].PC[j]);
                    }
                    FFUtilities.Write("\n----------AXIOM PRE COND OF:");
                    for (j = 0; j < FF.CF.gft_conn[i].num_axPC; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gft_conn[i].axPC[j]);
                    }
                    FFUtilities.Write("\n----------NON-AXIOM PRE COND OF:");
                    for (j = 0; j < FF.CF.gft_conn[i].num_naxPC; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gft_conn[i].naxPC[j]);
                    }
                    FFUtilities.Write("\n----------ADD BY:");
                    for (j = 0; j < FF.CF.gft_conn[i].num_A; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gft_conn[i].A[j]);
                    }
                    FFUtilities.Write("\n----------DEL BY:");
                    for (j = 0; j < FF.CF.gft_conn[i].num_D; j++)
                    {
                        FFUtilities.Write("\neffect %d", FF.CF.gft_conn[i].D[j]);
                    }
                }
            }

        }




    }
}
