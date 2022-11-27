using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;



using static CPORLib.FFCS.Output;
using static CPORLib.FFCS.Constants;



namespace CPORLib.FFCS
{
    public class Relax
    {



        /*********************************************************************
         * File: relax.c
         * Description: this file handles the relaxed planning problem, i.e.,
         *              the code is responsible for the heuristic evaluation
         *              of states during search.
         *
         *              --- THE HEART PEACE OF THE FF PLANNER ! ---
         *
         *              - fast (time critical) computation of the relaxed fixpoint
         *              - extraction of as short as possible plans, without search
         *
         *
         *
         *  ----- UPDATED VERSION TO HANDLE NORMALIZED ADL OPERATORS -----
         *
         *
         *
         * Author: Joerg Hoffmann 2000
         *
         *********************************************************************/




















        /* local globals
         */








        /* in agenda driven algorithm, the current set of goals is this
         */
         FFState lcurrent_goals;



        /* fixpoint
         */
         int[] lF;
         int lnum_F;
         int[] lE;
         int lnum_E;

         int[] lch_E;
         int lnum_ch_E;

         int[] l0P_E;
         int lnum_0P_E;

         int[] l0P_axE;
         int lnum_0P_axE;
         int[] l0P_naxE;
         int lnum_0P_naxE;





        /* 1P extraction
         */
         int[,] lgoals_at;
         int[] lnum_goals_at;

         int[] lch_F;
         int lnum_ch_F;

         int[] lused_O;
         int lnum_used_O;

         int lh;

         bool lonly_ax, lonly_nax;








        /*************************************
         * helper, for -1 == INFINITY method *
         *************************************/












        public  bool LESS(int a, int b)

        {

            if (a == INFINITY)
            {
                return false;
            }

            if (b == INFINITY)
            {
                return true;
            }

            return a < b;

        }












        /***********************************
         * FUNCTIONS ACCESSED FROM OUTSIDE *
         ***********************************/











        public  void initialize_relax()

        {

            int i;

            lcurrent_goals = new FFState(FF.CF.gnum_ft_conn);
            lcurrent_goals.max_F = FF.CF.gnum_ft_conn;

            lF = new int[FF.CF.gnum_ft_conn];// (int[])calloc(, sizeof(int));
            lE = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));
            lch_E = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));
            l0P_E = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));
            l0P_axE = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));
            l0P_naxE = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));

            lonly_ax = false;
            lonly_nax = false;

            /* initialize connectivity graph members for
             * relaxed planning
             */
            lnum_0P_E = 0;
            lnum_0P_axE = 0;
            lnum_0P_naxE = 0;
            for (i = 0; i < FF.CF.gnum_ef_conn; i++)
            {
                FF.CF.gef_conn[i].level = INFINITY;
                FF.CF.gef_conn[i].in_E = false;
                FF.CF.gef_conn[i].num_active_PCs = 0;
                FF.CF.gef_conn[i].ch = false;

                if (FF.CF.gef_conn[i].num_PC == 0)
                {
                    l0P_E[lnum_0P_E++] = i;
                    if (FF.CF.gop_conn[FF.CF.gef_conn[i].op].axiom)
                    {
                        l0P_axE[lnum_0P_axE++] = i;
                    }
                    else
                    {
                        l0P_naxE[lnum_0P_naxE++] = i;
                    }
                }
            }
            if (gcmd_line.debug >= 1)
            {
                FFUtilities.Write("\n\n----------------------------------------------0PE: ");
                for (i = 0; i < lnum_0P_E; i++)
                {
                    FFUtilities.Write("\n");
                    print_op_name(FF.CF.gef_conn[l0P_E[i]].op);
                }
                FFUtilities.Write("\n\n----------------------------------------------0PaxE: ");
                for (i = 0; i < lnum_0P_axE; i++)
                {
                    FFUtilities.Write("\n");
                    print_op_name(FF.CF.gef_conn[l0P_axE[i]].op);
                }
                FFUtilities.Write("\n\n----------------------------------------------0PnaxE: ");
                for (i = 0; i < lnum_0P_naxE; i++)
                {
                    FFUtilities.Write("\n");
                    print_op_name(FF.CF.gef_conn[l0P_naxE[i]].op);
                }
            }
            for (i = 0; i < FF.CF.gnum_op_conn; i++)
            {
                FF.CF.gop_conn[i].is_in_naxA = false;
                FF.CF.gop_conn[i].is_in_axA = false;
                FF.CF.gop_conn[i].is_in_H = false;
            }
            for (i = 0; i < FF.CF.gnum_ft_conn; i++)
            {
                FF.CF.gft_conn[i].level = INFINITY;
                FF.CF.gft_conn[i].in_F = false;
            }

            for (i = 0; i < FF.CF.gnum_ft_conn; i++)
            {
                FF.CF.gft_conn[i].is_true = INFINITY;
                FF.CF.gft_conn[i].is_goal = 0;
                FF.CF.gft_conn[i].ch = false;
            }
            for (i = 0; i < FF.CF.gnum_op_conn; i++)
            {
                FF.CF.gop_conn[i].is_used = INFINITY;
            }
            for (i = 0; i < FF.CF.gnum_ef_conn; i++)
            {
                FF.CF.gef_conn[i].in_plan = false;
            }
            lch_F = new int[FF.CF.gnum_ft_conn];// (int[])calloc(, sizeof(int));
            lnum_ch_F = 0;
            lused_O = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
            lnum_used_O = 0;
            FF.Planning.gin_plan_E = new int[FF.CF.gnum_ef_conn];// (int[])calloc(, sizeof(int));
            FF.Planning.gnum_in_plan_E = 0;

        }



        public  int get_1P_and_H(FFState S, FFState current_goals)

        {

            int h, max;

            source_to_dest(lcurrent_goals, current_goals);

            FF.Search.gevaluated_states++;

            max = build_fixpoint(S);
            h = extract_1P(max, true);

            if (gcmd_line.display_info == 122)
            {
                print_fixpoint_result();
            }

            reset_fixpoint();

            return h;

        }

         void source_to_dest(FFState dest, FFState source)

        {

            int i;

            for (i = 0; i < source.num_F; i++)
            {
                dest.F[i] = source.F[i];
            }
            dest.num_F = source.num_F;

        }

        public  int get_1P(FFState S, FFState current_goals)

        {

            int h, max;

            source_to_dest(lcurrent_goals, current_goals);

            FF.Search.gevaluated_states++;

            max = build_fixpoint(S);
            h = extract_1P(max, false);

            if (gcmd_line.display_info == 122)
            {
                print_fixpoint_result();
            }

            reset_fixpoint();

            return h;

        }



        public  void get_naxA(FFState S)
        {

            int i;

            lonly_ax = false;
            lonly_nax = true;

            lnum_E = 0;
            lnum_ch_E = 0;

            lnum_F = 0;
            for (i = 0; i < S.num_F; i++)
            {
                if (FF.CF.gft_conn[S.F[i]].in_F)
                {
                    continue;
                }
                new_fact(S.F[i]);
            }
            for (i = 0; i < lnum_F; i++)
            {
                activate_ft(lF[i], 0);
            }

            for (i = 0; i < lnum_0P_naxE; i++)
            {
                if (FF.CF.gef_conn[l0P_naxE[i]].in_E)
                {
                    continue;
                }
                new_ef(l0P_naxE[i]);
            }

            collect_naxA_info();

            reset_fixpoint();

            lonly_ax = false;
            lonly_nax = false;

        }



         void collect_naxA_info()

        {

            bool first_call = true;

            int i;

            if (first_call)
            {
                FF.Search.gnaxA = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
                FF.Search.gnum_naxA = 0;
                first_call = false;
            }

            for (i = 0; i < FF.Search.gnum_naxA; i++)
            {
                FF.CF.gop_conn[FF.Search.gnaxA[i]].is_in_naxA = false;
            }
            FF.Search.gnum_naxA = 0;

            for (i = 0; i < lnum_E; i++)
            {
                if (FF.CF.gop_conn[FF.CF.gef_conn[lE[i]].op].is_in_naxA)
                {
                    continue;
                }

                FF.CF.gop_conn[FF.CF.gef_conn[lE[i]].op].is_in_naxA = true;
                FF.Search.gnaxA[FF.Search.gnum_naxA++] = FF.CF.gef_conn[lE[i]].op;
            }

        }



        public  void get_axA(FFState S)

        {

            int i;

            lonly_ax = true;
            lonly_nax = false;

            lnum_E = 0;
            lnum_ch_E = 0;

            lnum_F = 0;
            for (i = 0; i < S.num_F; i++)
            {
                if (FF.CF.gft_conn[S.F[i]].in_F)
                {
                    continue;
                }
                new_fact(S.F[i]);
            }
            for (i = 0; i < lnum_F; i++)
            {
                activate_ft(lF[i], 0);
            }

            for (i = 0; i < lnum_0P_axE; i++)
            {
                if (FF.CF.gef_conn[l0P_axE[i]].in_E)
                {
                    continue;
                }
                new_ef(l0P_axE[i]);
            }

            collect_axA_info();

            reset_fixpoint();

            lonly_ax = false;
            lonly_nax = false;

        }



         void collect_axA_info()

        {

            bool first_call = true;

            int i;

            if (first_call)
            {
                FF.Search.gaxA = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
                FF.Search.gnum_axA = 0;
                first_call = false;
            }

            for (i = 0; i < FF.Search.gnum_axA; i++)
            {
                FF.CF.gop_conn[FF.Search.gaxA[i]].is_in_axA = false;
            }
            FF.Search.gnum_axA = 0;

            for (i = 0; i < lnum_E; i++)
            {
                if (FF.CF.gop_conn[FF.CF.gef_conn[lE[i]].op].is_in_axA)
                {
                    continue;
                }

                FF.CF.gop_conn[FF.CF.gef_conn[lE[i]].op].is_in_axA = true;
                FF.Search.gaxA[FF.Search.gnum_axA++] = FF.CF.gef_conn[lE[i]].op;
            }

        }















        /*******************************
         * RELAXED FIXPOINT ON A STATE *
         *******************************/
















         int build_fixpoint(FFState S)

        {

            int start_ft, stop_ft, start_ef, stop_ef, i, time = 0;

            initialize_fixpoint(S);

            start_ft = 0;
            start_ef = 0;
            while (true)
            {
                if (all_goals_activated(time))
                {
                    break;
                }

                stop_ft = lnum_F;
                for (i = start_ft; i < stop_ft; i++)
                {
                    activate_ft(lF[i], time);
                }

                if (time == 0)
                {
                    for (i = 0; i < lnum_0P_E; i++)
                    {
                        if (FF.CF.gef_conn[l0P_E[i]].in_E)
                        {
                            continue;
                        }
                        new_ef(l0P_E[i]);
                    }
                }

                stop_ef = lnum_E;
                for (i = start_ef; i < stop_ef; i++)
                {
                    activate_ef(lE[i], time);
                }

                if (stop_ft == lnum_F)
                {
                    break;
                }

                start_ft = stop_ft;
                start_ef = stop_ef;
                time++;
            }

            return time;

        }



         void initialize_fixpoint(FFState S)

        {

            int i;

            lnum_E = 0;
            lnum_ch_E = 0;

            lnum_F = 0;
            for (i = 0; i < S.num_F; i++)
            {
                if (FF.CF.gft_conn[S.F[i]].in_F)
                {
                    continue;
                }
                new_fact(S.F[i]);
            }

        }



         void activate_ft(int index, int time)

        {

            int i;

            FF.CF.gft_conn[index].level = time;

            if (!lonly_ax && !lonly_nax)
            {
                for (i = 0; i < FF.CF.gft_conn[index].num_PC; i++)
                {
                    FF.CF.gef_conn[FF.CF.gft_conn[index].PC[i]].num_active_PCs++;
                    if (!FF.CF.gef_conn[FF.CF.gft_conn[index].PC[i]].ch)
                    {
                        FF.CF.gef_conn[FF.CF.gft_conn[index].PC[i]].ch = true;
                        lch_E[lnum_ch_E++] = FF.CF.gft_conn[index].PC[i];
                    }
                    if (FF.CF.gef_conn[FF.CF.gft_conn[index].PC[i]].num_active_PCs ==
                         FF.CF.gef_conn[FF.CF.gft_conn[index].PC[i]].num_PC)
                    {
                        new_ef(FF.CF.gft_conn[index].PC[i]);
                    }
                }
            }

            if (lonly_ax)
            {
                for (i = 0; i < FF.CF.gft_conn[index].num_axPC; i++)
                {
                    FF.CF.gef_conn[FF.CF.gft_conn[index].axPC[i]].num_active_PCs++;
                    if (!FF.CF.gef_conn[FF.CF.gft_conn[index].axPC[i]].ch)
                    {
                        FF.CF.gef_conn[FF.CF.gft_conn[index].axPC[i]].ch = true;
                        lch_E[lnum_ch_E++] = FF.CF.gft_conn[index].axPC[i];
                    }
                    if (FF.CF.gef_conn[FF.CF.gft_conn[index].axPC[i]].num_active_PCs ==
                         FF.CF.gef_conn[FF.CF.gft_conn[index].axPC[i]].num_PC)
                    {
                        new_ef(FF.CF.gft_conn[index].axPC[i]);
                    }
                }
            }

            if (lonly_nax)
            {
                for (i = 0; i < FF.CF.gft_conn[index].num_naxPC; i++)
                {
                    FF.CF.gef_conn[FF.CF.gft_conn[index].naxPC[i]].num_active_PCs++;
                    if (!FF.CF.gef_conn[FF.CF.gft_conn[index].naxPC[i]].ch)
                    {
                        FF.CF.gef_conn[FF.CF.gft_conn[index].naxPC[i]].ch = true;
                        lch_E[lnum_ch_E++] = FF.CF.gft_conn[index].naxPC[i];
                    }
                    if (FF.CF.gef_conn[FF.CF.gft_conn[index].naxPC[i]].num_active_PCs ==
                         FF.CF.gef_conn[FF.CF.gft_conn[index].naxPC[i]].num_PC)
                    {
                        new_ef(FF.CF.gft_conn[index].naxPC[i]);
                    }
                }
            }

        }



         void activate_ef(int index, int time)

        {

            int i;

            FF.CF.gef_conn[index].level = time;

            for (i = 0; i < FF.CF.gef_conn[index].num_A; i++)
            {
                if (FF.CF.gft_conn[FF.CF.gef_conn[index].A[i]].in_F)
                {
                    continue;
                }
                new_fact(FF.CF.gef_conn[index].A[i]);
            }

        }



         void new_fact(int index)

        {

            lF[lnum_F++] = index;
            FF.CF.gft_conn[index].in_F = true;

        }



         void new_ef(int index)

        {

            lE[lnum_E++] = index;
            FF.CF.gef_conn[index].in_E = true;

        }



         void reset_fixpoint()

        {

            int i;

            for (i = 0; i < lnum_F; i++)
            {
                FF.CF.gft_conn[lF[i]].level = INFINITY;
                FF.CF.gft_conn[lF[i]].in_F = false;
            }

            for (i = 0; i < lnum_E; i++)
            {
                FF.CF.gef_conn[lE[i]].level = INFINITY;
                FF.CF.gef_conn[lE[i]].in_E = false;
            }

            for (i = 0; i < lnum_ch_E; i++)
            {
                FF.CF.gef_conn[lch_E[i]].num_active_PCs = 0;
                FF.CF.gef_conn[lch_E[i]].ch = false;
            }

        }



         bool all_goals_activated(int time)

        {

            int i;

            for (i = 0; i < lcurrent_goals.num_F; i++)
            {
                if (!FF.CF.gft_conn[lcurrent_goals.F[i]].in_F)
                {
                    return false;
                }
            }

            for (i = 0; i < lcurrent_goals.num_F; i++)
            {
                if (FF.CF.gft_conn[lcurrent_goals.F[i]].level == INFINITY)
                {
                    FF.CF.gft_conn[lcurrent_goals.F[i]].level = time;
                }
            }

            return true;

        }



         void print_fixpoint_result()

        {

            int time, i;
            bool hit, hit_F, hit_E;

            time = 0;
            while (true)
            {
                hit = false;
                hit_F = false;
                hit_E = false;
                for (i = 0; i < FF.CF.gnum_ft_conn; i++)
                {
                    if (FF.CF.gft_conn[i].level == time)
                    {
                        hit = true;
                        hit_F = true;
                        break;
                    }
                }
                for (i = 0; i < FF.CF.gnum_ef_conn; i++)
                {
                    if (FF.CF.gef_conn[i].level == time)
                    {
                        hit = true;
                        hit_E = true;
                        break;
                    }
                }
                if (!hit)
                {
                    break;
                }

                FFUtilities.Write("\n\nLEVEL %d:", time);
                if (hit_F)
                {
                    FFUtilities.Write("\n\nFACTS:");
                    for (i = 0; i < FF.CF.gnum_ft_conn; i++)
                    {
                        if (FF.CF.gft_conn[i].level == time)
                        {
                            FFUtilities.Write("\n");
                            print_ft_name(i);
                        }
                    }
                }
                if (hit_E)
                {
                    FFUtilities.Write("\n\nEFS:");
                    for (i = 0; i < FF.CF.gnum_ef_conn; i++)
                    {
                        if (FF.CF.gef_conn[i].level == time)
                        {
                            FFUtilities.Write("\neffect %d to ", i);
                            print_op_name(FF.CF.gef_conn[i].op);
                        }
                    }
                }

                time++;
            }

        }













        /**************************************
         * FIRST RELAXED PLAN (1P) EXTRACTION *
         **************************************/













         int extract_1P(int max, bool H_info)

        {

            int max_goal_level, time;

            reset_search_info();

            if ((max_goal_level = initialize_goals(max)) == INFINITY)
            {
                return INFINITY;
            }

            lh = 0;
            for (time = max_goal_level; time > 0; time--)
            {
                achieve_goals(time);
            }
            if (H_info)
            {
                collect_H_info();
            }

            return lh;

        }



        int initialize_goals(int max)

        {

            bool first_call = true;
            int highest_seen = 0;

            int i, max_goal_level, ft;

            if (first_call)
            {
                lgoals_at = new int[RELAXED_STEPS_DEFAULT,FF.CF.gnum_ft_conn];// (int[]*)calloc(, sizeof(int[]));
                lnum_goals_at = new int[RELAXED_STEPS_DEFAULT];// (int[])calloc(, sizeof(int));
                
                highest_seen = RELAXED_STEPS_DEFAULT;
                first_call = false;
            }

            if (max + 1 > highest_seen)
            {

                highest_seen = max + 1;
                lgoals_at = new int[highest_seen, FF.CF.gnum_ft_conn];// (int[]*)calloc(, sizeof(int[]));
                lnum_goals_at = new int[highest_seen];// (int[])calloc(, sizeof(int));
            } 

            for (i = 0; i < max + 1; i++)
            {
                lnum_goals_at[i] = 0;
            }

            max_goal_level = 0;
            for (i = 0; i < lcurrent_goals.num_F; i++)
            {
                ft = lcurrent_goals.F[i];
                if (FF.CF.gft_conn[ft].level == INFINITY)
                {
                    return INFINITY;
                }
                if (FF.CF.gft_conn[ft].level > max_goal_level)
                {
                    max_goal_level = FF.CF.gft_conn[ft].level;
                }
                lgoals_at[FF.CF.gft_conn[ft].level,lnum_goals_at[FF.CF.gft_conn[ft].level]++] = ft;
                FF.CF.gft_conn[ft].is_goal = 1;
                if (!FF.CF.gft_conn[ft].ch)
                {
                    lch_F[lnum_ch_F++] = ft;
                    FF.CF.gft_conn[ft].ch = true;
                }
            }

            return max_goal_level;

        }



         void achieve_goals(int time)

        {

            int i, j, k, ft, min_p, min_e, ef, p, op;

            if (gcmd_line.display_info == 123)
            {
                FFUtilities.Write("\nselecting at step %3d: ", time - 1);
            }

            for (i = 0; i < lnum_goals_at[time]; i++)
            {
                ft = lgoals_at[time,i];

                if (FF.CF.gft_conn[ft].is_true == time)
                {
                    /* fact already added by prev now selected op
                     */
                    continue;
                }

                min_p = INFINITY;
                min_e = -1;
                for (j = 0; j < FF.CF.gft_conn[ft].num_A; j++)
                {
                    ef = FF.CF.gft_conn[ft].A[j];
                    if (FF.CF.gef_conn[ef].level != time - 1) continue;
                    p = 0;
                    for (k = 0; k < FF.CF.gef_conn[ef].num_PC; k++)
                    {
                        p += FF.CF.gft_conn[FF.CF.gef_conn[ef].PC[k]].level;
                    }
                    if (LESS(p, min_p))
                    {
                        min_p = p;
                        min_e = ef;
                    }
                }
                ef = min_e;
                op = FF.CF.gef_conn[ef].op;

                /* do not officially include axioms intothe rplan!
                 */
                if (!FF.CF.gop_conn[op].axiom)
                {
                    if (!FF.CF.gef_conn[ef].in_plan)
                    {
                        FF.CF.gef_conn[ef].in_plan = true;
                        FF.Planning.gin_plan_E[FF.Planning.gnum_in_plan_E++] = ef;
                    }
                    if (FF.CF.gop_conn[op].is_used != time)
                    {
                        if (FF.CF.gop_conn[op].is_used == INFINITY)
                        {
                            lused_O[lnum_used_O++] = op;
                        }
                        FF.CF.gop_conn[op].is_used = time;
                        lh++;
                        if (gcmd_line.display_info == 123)
                        {
                            print_op_name(op);
                            FFUtilities.Write("\n                       ");
                        }
                    }
                }
                else
                {
                    if (gcmd_line.display_info == 123)
                    {
                        print_op_name(op);
                        FFUtilities.Write(" - skipped: axiom\n                       ");
                    }
                }

                for (j = 0; j < FF.CF.gef_conn[ef].num_PC; j++)
                {
                    ft = FF.CF.gef_conn[ef].PC[j];
                    if (FF.CF.gft_conn[ft].is_true == time)
                    {
                        /* a prev at this level selected op accidently adds this precond, 
                         * so we can order that op before this one and get the precond added for free.
                         */
                        continue;
                    }
                    if (FF.CF.gft_conn[ft].is_goal == 1)
                    {
                        /* this fact already is a goal
                         */
                        continue;
                    }
                    lgoals_at[FF.CF.gft_conn[ft].level,lnum_goals_at[FF.CF.gft_conn[ft].level]++] = ft;
                    FF.CF.gft_conn[ft].is_goal = 1;
                    if (!FF.CF.gft_conn[ft].ch)
                    {
                        lch_F[lnum_ch_F++] = ft;
                        FF.CF.gft_conn[ft].ch = true;
                    }
                }

                for (j = 0; j < FF.CF.gef_conn[ef].num_A; j++)
                {
                    ft = FF.CF.gef_conn[ef].A[j];
                    FF.CF.gft_conn[ft].is_true = time;
                    /* NOTE: one level below a goal will only be skipped if it's true value is time-1,
                     * so subgoals introduced by prev selected ops are not excluded here.
                     *
                     * --- neither those of the at this level prev selected oned - which we want -
                     * nor those of at prev levels selected ops - which we would want to be skipped.
                     *
                     * --- so the ordering consraints assumed are valid but don't explore
                     * the full potential.
                     */
                    if (!FF.CF.gft_conn[ft].ch)
                    {
                        lch_F[lnum_ch_F++] = ft;
                        FF.CF.gft_conn[ft].ch = true;
                    }
                }
                for (j = 0; j < FF.CF.gef_conn[ef].num_I; j++)
                {
                    for (k = 0; k < FF.CF.gef_conn[FF.CF.gef_conn[ef].I[j]].num_A; k++)
                    {
                        ft = FF.CF.gef_conn[FF.CF.gef_conn[ef].I[j]].A[k];
                        FF.CF.gft_conn[ft].is_true = time;
                        if (!FF.CF.gft_conn[ft].ch)
                        {
                            lch_F[lnum_ch_F++] = ft;
                            FF.CF.gft_conn[ft].ch = true;
                        }
                    }
                }
            }

        }


         bool first_call = true;
         int[] H = null, D = null;

         void collect_H_info()

        {


            int num_H;
            int i, j, k, ft, ef, op, d;

            if (first_call)
            {
                FF.Search.gH = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
                H = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
                D = new int[FF.CF.gnum_op_conn];// (int[])calloc(, sizeof(int));
                FF.Search.gnum_H = 0;
                num_H = 0;
                first_call = false;
            }

            for (i = 0; i < FF.Search.gnum_H; i++)
            {
                FF.CF.gop_conn[FF.Search.gH[i]].is_in_H = false;
            }

            num_H = 0;
            for (i = 0; i < lnum_goals_at[1]; i++)
            {
                ft = lgoals_at[1,i];

                for (j = 0; j < FF.CF.gft_conn[ft].num_A; j++)
                {
                    ef = FF.CF.gft_conn[ft].A[j];
                    if (FF.CF.gef_conn[ef].level != 0)
                    {
                        continue;
                    }
                    if (FF.CF.gop_conn[FF.CF.gef_conn[ef].op].axiom) continue;

                    op = FF.CF.gef_conn[ef].op;

                    if (FF.CF.gop_conn[op].is_in_H)
                    {
                        continue;
                    }
                    FF.CF.gop_conn[op].is_in_H = true;
                    H[num_H++] = op;
                }
            }

            /* H collected; now order it
             * here: count number of goal- and subgoal facts that
             *       op deletes (with level 0 effects). order less deletes
             *       before more deletes.
             *       start from back of H, to prefer down under
             *       goals to upper goals.
             */
            FF.Search.gnum_H = 0;
            for (i = num_H - 1; i > -1; i--)
            {
                d = 0;
                for (j = 0; j < FF.CF.gop_conn[H[i]].num_E; j++)
                {
                    ef = FF.CF.gop_conn[H[i]].E[j];
                    if (FF.CF.gef_conn[ef].level != 0) continue;
                    for (k = 0; k < FF.CF.gef_conn[ef].num_D; k++)
                    {
                        if (FF.CF.gft_conn[FF.CF.gef_conn[ef].D[k]].is_goal == 1) d++;
                    }
                }
                for (j = 0; j < FF.Search.gnum_H; j++)
                {
                    if (D[j] > d) break;
                }
                for (k = FF.Search.gnum_H; k > j; k--)
                {
                    FF.Search.gH[k] = FF.Search.gH[k - 1];
                    D[k] = D[k - 1];
                }
                FF.Search.gH[j] = H[i];
                D[j] = d;
                FF.Search.gnum_H++;
            }
            if (gcmd_line.display_info == 124)
            {
                FFUtilities.Write("\ncollected H: ");
                for (i = 0; i < FF.Search.gnum_H; i++)
                {
                    print_op_name(FF.Search.gH[i]);
                    FFUtilities.Write("\n              ");
                }
            }

        }



         void reset_search_info()

        {

            int i;

            for (i = 0; i < lnum_ch_F; i++)
            {
                FF.CF.gft_conn[lch_F[i]].is_true = INFINITY;
                FF.CF.gft_conn[lch_F[i]].is_goal = 0;
                FF.CF.gft_conn[lch_F[i]].ch = false;
            }
            lnum_ch_F = 0;

            for (i = 0; i < lnum_used_O; i++)
            {
                FF.CF.gop_conn[lused_O[i]].is_used = INFINITY;
            }
            lnum_used_O = 0;

            for (i = 0; i < FF.Planning.gnum_in_plan_E; i++)
            {
                FF.CF.gef_conn[FF.Planning.gin_plan_E[i]].in_plan = false;
            }
            FF.Planning.gnum_in_plan_E = 0;

        }


    }
}
