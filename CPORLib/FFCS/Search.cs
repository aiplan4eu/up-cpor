using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;


using static CPORLib.FFCS.Output;

using static CPORLib.FFCS.Constants;
using static CPORLib.FFCS.FFUtilities;



namespace CPORLib.FFCS
{
    public class Search
    {



        /*********************************************************************
         *
         * File: search.c
         *
         * Description: implementation of routines that search the state space
         *
         *              ADL version, Goal Agenda driven
         *                           Enforced Hill-climbing enhanced with
         *                           informed Goal Added Deletion Heuristic,
         *
         *                           and, alternatively, standard Best First Search
         *
         *
         * Author: Joerg Hoffmann 2000
         *
         *********************************************************************/



        /*******************
         * SEARCHING NEEDS *
         *******************/

        /* the goal state, divided into subsets
         */
        public  FFState[] ggoal_agenda;
        public  int gnum_goal_agenda;



        /* byproduct of fixpoint: applicable actions
         */
        public  int[] gnaxA;
        public  int gnum_naxA;
        public  int[] gaxA;
        public  int gnum_axA;



        /* communication from extract 1.P. to search engines:
         * 1P action choice
         */
        public  int[] gH;
        public  int gnum_H;

        /* number of states that got heuristically evaluated
 */
        public  int gevaluated_states = 0;

        /* maximal depth of breadth first search
         */
        public  int gmax_search_depth = 0;


        /*****************
         * LOCAL GLOBALS *
         *****************/



        bool ltakeA;







        /* in agenda driven algorithm, the current set of goals is this
         */
        FFState lcurrent_goals;



        /* search space for EHC
         */
        EhcNode lehc_space_head, lehc_space_end, lehc_current_start, lehc_current_end;



        /* memory (hash table) for states that are already members
         * of the breadth - first search space in EHC
         */
        EhcHashEntry[] lehc_hash_entry = new EhcHashEntry[EHC_HASH_SIZE];
        int[] lnum_ehc_hash_entry = new int[EHC_HASH_SIZE];
        int[] lchanged_ehc_entrys = new int[EHC_HASH_SIZE];
        int lnum_changed_ehc_entrys;
        bool[] lchanged_ehc_entry = new bool[EHC_HASH_SIZE];



        /* memory (hash table) for states that are already 
         * encountered by current serial plan
         */
        PlanHashEntry[] lplan_hash_entry = new PlanHashEntry[PLAN_HASH_SIZE];



        /* search space
         */
        BfsNode lbfs_space_head, lbfs_space_had;



        /* memory (hash table) for states that are already members
         * of the best first search space
         */
        BfsHashEntry[] lbfs_hash_entry = new BfsHashEntry[BFS_HASH_SIZE];












        /********************************
         * EHC FUNCTION, CALLED BY MAIN *
         ********************************/







        bool first_call = true;

        FFState S, S_;

        public bool do_enforced_hill_climbing(FFState start, FFState end)
        {
            int i, h, h_ = 0;

            if (first_call)
            {
                /* on first call, initialize plan hash table, search space, search hash table
                 */
                for (i = 0; i < PLAN_HASH_SIZE; i++)
                {
                    lplan_hash_entry[i] = null;
                }
                /* on subsequent calls, the start is already hashed, as it's the end
                 * of the previous calls
                 */
                hash_plan_state(start, 0);

                lehc_space_head = new EhcNode();
                lehc_space_end = lehc_space_head;

                for (i = 0; i < EHC_HASH_SIZE; i++)
                {
                    lehc_hash_entry[i] = null;
                    lnum_ehc_hash_entry[i] = 0;
                    lchanged_ehc_entry[i] = false;
                }
                lnum_changed_ehc_entrys = 0;

                S = new FFState(FF.CF.gnum_ft_conn);
                S.max_F = FF.CF.gnum_ft_conn;
                S_ = new FFState(FF.CF.gnum_ft_conn);
                S_.max_F = FF.CF.gnum_ft_conn;

                lcurrent_goals = new FFState(FF.CF.gnum_ft_conn);
                lcurrent_goals.max_F = FF.CF.gnum_ft_conn;

                first_call = false;
            }

            /* start enforced Hill-climbing
             */

            source_to_dest(lcurrent_goals, end);
             
            source_to_dest(S, start);
            h = FF.RLX.get_1P_and_H(S, lcurrent_goals);

            if (h == INFINITY)
            {
                return false;
            }
            if (h == 0)
            {
                return true;
            }
            FFUtilities.Write("\n\nCueing down from goal distance: " + h + " into depth ");

            while (h != 0)
            {
                ltakeA = false;
                if (!search_for_better_state(S, h, S_, out h_))
                {
                    /* H space got empty, switch to complete space
                     */
                    if (gcmd_line.display_info != 0)
                    {
                        FFUtilities.Write("\n                                                H search space got empty !");
                        FFUtilities.Write("\n                                                switching to complete search space now.");
                        FFUtilities.Write("\n                                                ");
                    }
                    ltakeA = true;
                    if (!search_for_better_state(S, h, S_, out h_))
                    {
                        return false;
                    }
                }
                source_to_dest(S, S_);
                h = h_;
                FFUtilities.Write("\n                                " + h + "            ");
            }

            return true;

        }











        /*************************************************
         * FUNCTIONS FOR BREADTH FIRST SEARCH IN H SPACE *
         *************************************************/











        bool first_call2 = true;
        FFState S__;


        public bool search_for_better_state(FFState S, int h, FFState S_, out int h_)
        {
            int i, h__, depth = 0, g;
            EhcNode tmp;

            if (first_call2)
            {
                S__ = new FFState(FF.CF.gnum_ft_conn);
                S__.max_F = FF.CF.gnum_ft_conn;
                first_call2 = false;
            }

            /* don't hash states, but search nodes.
             * this way, don't need to keep states twice in memory
             */
            tmp = new EhcNode();
            copy_source_to_dest((tmp.S), S);
            hash_ehc_node(tmp);

            lehc_current_end = lehc_space_head.next;
            if (!ltakeA)
            {
                for (i = 0; i < gnum_H; i++)
                {
                    g = result_to_dest(S__, S, gH[i]);
                    add_to_ehc_space(S__, gH[i], null, g);
                }
            }
            else
            {
                FF.RLX.get_naxA(S);
                for (i = 0; i < gnum_naxA; i++)
                {
                    g = result_to_dest(S__, S, gnaxA[i]);
                    add_to_ehc_space(S__, gnaxA[i], null, g);
                }
            }
            lehc_current_start = lehc_space_head.next;

            while (true)
            {
                if (lehc_current_start == lehc_current_end)
                {
                    reset_ehc_hash_entrys();
                    //free(tmp);
                    h_ = INFINITY;
                    return false;
                }
                if (lehc_current_start.depth > depth)
                {
                    depth = lehc_current_start.depth;
                    if (depth > gmax_search_depth)
                    {
                        gmax_search_depth = depth;
                    }
                    FFUtilities.Write("[" + depth + "]");
                }
                h__ = expand_first_node(h);
                if (FF.RLX.LESS(h__, h))
                {
                    break;
                }
            }

            reset_ehc_hash_entrys();
            //free(tmp);

            extract_plan_fragment(S);

            source_to_dest(S_, (lehc_current_start.S));
            h_ = h__;

            return true;

        }



        void add_to_ehc_space(FFState S, int op, EhcNode father, int new_goal)

        {

            /* see if state is already a part of this search space
             */
            if (ehc_state_hashed(S))
            {
                return;
            }

            if (lehc_current_end == null)
            {
                lehc_current_end = new EhcNode();
                lehc_space_end.next = lehc_current_end;
                lehc_space_end = lehc_current_end;
            }

            copy_source_to_dest(lehc_current_end.S, S);
            lehc_current_end.op = op;
            lehc_current_end.father = father;
            if (father == null)
            {
                lehc_current_end.depth = 1;
            }
            else
            {
                lehc_current_end.depth = father.depth + 1;
            }
            lehc_current_end.new_goal = new_goal;

            hash_ehc_node(lehc_current_end);

            lehc_current_end = lehc_current_end.next;

        }


        bool fc = true;
        FFState S_2;

        int expand_first_node(int h)
        {
            int h_, i, g;

            if (fc)
            {
                S_2 = new FFState(FF.CF.gnum_ft_conn);
                S_2.max_F = FF.CF.gnum_ft_conn;
                fc = false;
            }

            h_ = FF.RLX.get_1P_and_H((lehc_current_start.S), lcurrent_goals);

            if (h_ == INFINITY)
            {
                lehc_current_start = lehc_current_start.next;
                return h_;
            }

            if (lehc_current_start.new_goal != -1 &&
                 new_goal_gets_deleted(lehc_current_start))
            {
                lehc_current_start = lehc_current_start.next;
                return INFINITY;
            }

            if (h_ < h)
            {
                return h_;
            }

            if (!ltakeA)
            {
                for (i = 0; i < gnum_H; i++)
                {
                    g = result_to_dest(S_2, (lehc_current_start.S), gH[i]);
                    add_to_ehc_space(S_2, gH[i], lehc_current_start, g);
                }
            }
            else
            {
                FF.RLX.get_naxA((lehc_current_start.S));
                for (i = 0; i < gnum_naxA; i++)
                {
                    g = result_to_dest(S_2, (lehc_current_start.S), gnaxA[i]);
                    add_to_ehc_space(S_2, gnaxA[i], lehc_current_start, g);
                }
            }

            lehc_current_start = lehc_current_start.next;

            return h_;

        }











        /********************************************************
         * HASHING ALGORITHM FOR RECOGNIZING REPEATED STATES IN *
         * EHC BREADTH FIRST SEARCH                             *
         ********************************************************/












        void hash_ehc_node(EhcNode n)

        {

            int i, sum, index;
            EhcHashEntry h, prev = null;

            sum = state_sum((n.S));
            index = sum & EHC_HASH_BITS;

            h = lehc_hash_entry[index];
            if (h == null)
            {
                h = new EhcHashEntry();
                h.sum = sum;
                h.ehc_node = n;
                lehc_hash_entry[index] = h;
                lnum_ehc_hash_entry[index]++;
                if (!lchanged_ehc_entry[index])
                {
                    lchanged_ehc_entrys[lnum_changed_ehc_entrys++] = index;
                    lchanged_ehc_entry[index] = true;
                }
                return;
            }
            i = 0;
            while (h != null)
            {
                if (i == lnum_ehc_hash_entry[index])
                {
                    break;
                }
                i++;
                prev = h;
                h = h.next;
            }

            if (h != null)
            {
                /* current list end is still in allocated list of hash entrys
                 */
                h.sum = sum;
                h.ehc_node = n;
                lnum_ehc_hash_entry[index]++;
                if (!lchanged_ehc_entry[index])
                {
                    lchanged_ehc_entrys[lnum_changed_ehc_entrys++] = index;
                    lchanged_ehc_entry[index] = true;
                }
                return;
            }
            /* allocated list ended; connect a new hash entry to it.
             */
            h = new EhcHashEntry();
            h.sum = sum;
            h.ehc_node = n;
            prev.next = h;
            lnum_ehc_hash_entry[index]++;
            if (!lchanged_ehc_entry[index])
            {
                lchanged_ehc_entrys[lnum_changed_ehc_entrys++] = index;
                lchanged_ehc_entry[index] = true;
            }
            return;

        }



        bool ehc_state_hashed(FFState S)

        {

            int i, sum, index;
            EhcHashEntry h;

            sum = state_sum(S);
            index = sum & EHC_HASH_BITS;

            h = lehc_hash_entry[index];
            for (i = 0; i < lnum_ehc_hash_entry[index]; i++)
            {
                if (h.sum != sum)
                {
                    h = h.next;
                    continue;
                }
                if (same_state((h.ehc_node.S), S))
                {
                    return true;
                }
                h = h.next;
            }

            return false;

        }



        bool same_state(FFState S1, FFState S2)

        {

            int i, j;

            if (S2.num_F != S1.num_F)
            {
                return false;
            }

            for (i = 0; i < S2.num_F; i++)
            {
                for (j = 0; j < S1.num_F; j++)
                {
                    if (S1.F[j] == S2.F[i])
                    {
                        break;
                    }
                }
                if (j == S1.num_F)
                {
                    return false;
                }
            }

            return true;

        }



        int state_sum(FFState S)

        {

            int i, sum = 0;

            for (i = 0; i < S.num_F; i++)
            {
                sum += FF.CF.gft_conn[S.F[i]].rand;
            }

            return sum;

        }



        void reset_ehc_hash_entrys()

        {

            int i;

            for (i = 0; i < lnum_changed_ehc_entrys; i++)
            {
                lnum_ehc_hash_entry[lchanged_ehc_entrys[i]] = 0;
                lchanged_ehc_entry[lchanged_ehc_entrys[i]] = false;
            }
            lnum_changed_ehc_entrys = 0;

        }











        /***************************************************
         * FUNCTIONS FOR UPDATING THE CURRENT SERIAL PLAN, *
         * BASED ON SEARCH SPACE INFORMATION .             *
         *                                                 *
         * EMPLOY SOMEWHAT TEDIOUS HASHING PROCEDURE TO    *
         * AVOID REPEATED STATES IN THE PLAN               *
         ***************************************************/












        public void extract_plan_fragment(FFState S)

        {

            EhcNode i;
            int[] ops = new int[MAX_PLAN_LENGTH];
            int num_ops;
            FFState[] states = new FFState[MAX_PLAN_LENGTH];
            int j;
            PlanHashEntry start = null, i_ph;

            num_ops = 0;
            for (i = lehc_current_start; i != null; i = i.father)
            {
                if ((start = plan_state_hashed((i.S))) != null)
                {
                    for (i_ph = start.next_step; i_ph != null; i_ph = i_ph.next_step)
                    {
                        i_ph.step = -1;
                    }
                    FF.Planning.gnum_plan_ops = start.step;
                    break;
                }
                if (num_ops == MAX_PLAN_LENGTH)
                {
                    FFUtilities.Write("\nincrease MAX_PLAN_LENGTH! currently %d\n\n",
                       MAX_PLAN_LENGTH);
                    Exit(1);
                }
                states[num_ops] = (i.S);
                ops[num_ops++] = i.op;
            }
            if (start == null)
            {
                start = plan_state_hashed(S);
                if (start == null)
                {
                    FFUtilities.Write("\n\ncurrent start state not hashed! debug me!\n\n");
                    Exit(1);
                }
                if (start.step == -1)
                {
                    FFUtilities.Write("\n\ncurrent start state marked removed from plan! debug me!\n\n");
                    Exit(1);
                }
            }

            for (j = num_ops - 1; j > -1; j--)
            {
                if (FF.Planning.gnum_plan_ops == MAX_PLAN_LENGTH)
                {
                    FFUtilities.Write("\nincrease MAX_PLAN_LENGTH! currently %d\n\n",
                       MAX_PLAN_LENGTH);
                    Exit(1);
                }
                start.next_step = hash_plan_state(states[j], FF.Planning.gnum_plan_ops + 1);
                start = start.next_step;
                source_to_dest((FF.Planning.gplan_states[FF.Planning.gnum_plan_ops + 1]), states[j]);
                FF.Planning.gplan_ops[FF.Planning.gnum_plan_ops++] = ops[j];
            }

        }




        public PlanHashEntry hash_plan_state(FFState S, int step)

        {

            int sum, index;
            PlanHashEntry h, tmp;

            sum = state_sum(S);
            index = sum & PLAN_HASH_BITS;

            for (h = lplan_hash_entry[index]; h != null; h = h.next)
            {
                if (h.sum != sum) continue;
                if (same_state(S, (h.S))) break;
            }

            if (h != null)
            {
                if (h.step != -1)
                {
                    FFUtilities.Write("\n\nreencountering a state that is already in plan! debug me\n\n");
                    Exit(1);
                }
                h.step = step;
                return h;
            }

            for (h = lplan_hash_entry[index]; h != null && h.next != null; h = h.next) ;

            tmp = new PlanHashEntry();
            tmp.sum = sum;
            copy_source_to_dest((tmp.S), S);
            tmp.step = step;

            if (h != null)
            {
                h.next = tmp;
            }
            else
            {
                lplan_hash_entry[index] = tmp;
            }

            return tmp;

        }



        public PlanHashEntry plan_state_hashed(FFState S)

        {

            int sum, index;
            PlanHashEntry h;

            sum = state_sum(S);
            index = sum & PLAN_HASH_BITS;

            for (h = lplan_hash_entry[index]; h != null; h = h.next)
            {
                if (h.sum != sum) continue;
                if (same_state(S, (h.S))) break;
            }

            if (h != null && h.step != -1)
            {
                return h;
            }

            return null;

        }














        /*********************************
         * ADDED GOAL DELETION HEURISTIC *
         *********************************/













         bool new_goal_gets_deleted(EhcNode n)

        {

            int i, j, ef, new_goal = n.new_goal;

            for (i = 0; i < FF.Planning.gnum_in_plan_E; i++)
            {
                ef = FF.Planning.gin_plan_E[i];
                for (j = 0; j < FF.CF.gef_conn[ef].num_D; j++)
                {
                    if (FF.CF.gef_conn[ef].D[j] == new_goal)
                    {
                        return true;
                    }
                }
            }

            return false;

        }















        /************************************
         * BEST FIRST SEARCH IMPLEMENTATION *
         ************************************/














         bool fc3 = true;
         FFState S3;

        public bool do_best_first_search()

        {

            BfsNode first;
            int i, min = INFINITY;
            bool start = true;

            if (fc3)
            {
                S3 = new FFState(FF.CF.gnum_ft_conn);
                S3.max_F = FF.CF.gnum_ft_conn;
                fc3 = false;
            }

            lbfs_space_head = new BfsNode();
            lbfs_space_had = null;

            for (i = 0; i < BFS_HASH_SIZE; i++)
            {
                lbfs_hash_entry[i] = null;
            }

            add_to_bfs_space(FF.DP.ginitial_state, -1, null);

            while (true)
            {
                if ((first = lbfs_space_head.next) == null)
                {
                    FFUtilities.Write("\n\nbest first search space empty! problem proven unsolvable.\n\n");
                    return false;
                }

                lbfs_space_head.next = first.next;
                if (first.next != null)
                {
                    first.next.prev = lbfs_space_head;
                }

                if (FF.RLX.LESS(first.h, min))
                {
                    min = first.h;
                    if (start)
                    {
                        FFUtilities.Write("\nadvancing to distance : %d", min);
                        start = false;
                    }
                    else
                    {
                        FFUtilities.Write("\n                        %d", min);
                    }
                }

                if (first.h == 0)
                {
                    break;
                }

                FF.RLX.get_naxA((first.S));
                if (gcmd_line.debug >= 3)
                {
                    FFUtilities.Write("\n\napplicable actions:");
                    for (i = 0; i < gnum_naxA; i++)
                    {
                        FFUtilities.Write("\n"); print_op_name(gnaxA[i]);
                    }
                }
                for (i = 0; i < gnum_naxA; i++)
                {
                    /* DEBUG
                     */
                    if (FF.CF.gop_conn[gnaxA[i]].axiom)
                    {
                        FFUtilities.Write("\nreal A axiom??\n\n");
                        print_op_name(gnaxA[i]);
                        Exit(1);
                    }
                    result_to_dest(S3, (first.S), gnaxA[i]);
                    add_to_bfs_space(S3, gnaxA[i], first);
                }

                first.next = lbfs_space_had;
                lbfs_space_had = first;
            }

            extract_plan(first);
            return true;

        }



        void add_to_bfs_space(FFState S, int op, BfsNode father)

        {

            BfsNode newNode, i;
            int h;

            /* see if state is already a part of this search space
             */
            if (bfs_state_hashed(S))
            {
                return;
            }

            h = FF.RLX.get_1P(S, FF.DP.ggoal_state);

            if (h == INFINITY)
            {
                return;
            }

            for (i = lbfs_space_head; i.next != null; i = i.next)
            {
                if (i.next.h > h) break;
            }

            newNode = new BfsNode();
            copy_source_to_dest(newNode.S, S);
            newNode.op = op;
            newNode.h = h;
            newNode.father = father;

            newNode.next = i.next;
            newNode.prev = i;
            i.next = newNode;
            if (newNode.next != null)
            {
                newNode.next.prev = newNode;
            }

            hash_bfs_node(newNode);

        }



        void extract_plan(BfsNode last)

        {

            BfsNode i;
            int[] ops = new int[MAX_PLAN_LENGTH];
            int num_ops;
            int j;

            num_ops = 0;
            for (i = last; i.op != -1; i = i.father)
            {
                if (num_ops == MAX_PLAN_LENGTH)
                {
                    FFUtilities.Write("\nincrease MAX_PLAN_LENGTH! currently %d\n\n",
                       MAX_PLAN_LENGTH);
                    Exit(1);
                }
                ops[num_ops++] = i.op;
            }

            FF.Planning.gnum_plan_ops = 0;
            for (j = num_ops - 1; j > -1; j--)
            {
                FF.Planning.gplan_ops[FF.Planning.gnum_plan_ops++] = ops[j];
            }

        }












        /************************************************************
         * HASHING ALGORITHM FOR RECOGNIZING REPEATED STATES IN BFS *
         ************************************************************/












        void hash_bfs_node(BfsNode n)

        {

            int sum, index;
            BfsHashEntry h, tmp;

            sum = state_sum((n.S));
            index = sum & BFS_HASH_BITS;

            h = lbfs_hash_entry[index];
            if (h == null)
            {
                h = new BfsHashEntry();
                h.sum = sum;
                h.bfs_node = n;
                lbfs_hash_entry[index] = h;
                return;
            }
            for (; h.next != null; h = h.next) ;

            tmp = new BfsHashEntry();
            tmp.sum = sum;
            tmp.bfs_node = n;
            h.next = tmp;

        }



        bool bfs_state_hashed(FFState S)

        {

            int sum, index;
            BfsHashEntry h;

            sum = state_sum(S);
            index = sum & BFS_HASH_BITS;

            h = lbfs_hash_entry[index];
            for (h = lbfs_hash_entry[index]; h != null; h = h.next)
            {
                if (h.sum != sum)
                {
                    continue;
                }
                if (same_state((h.bfs_node.S), S))
                {
                    return true;
                }
            }

            return false;

        }












        /****************************
         * STATE HANDLING FUNCTIONS *
         ****************************/












        /* function that computes state transition as induced by a
         * normalized ADL action. Adds go before deletes!
         *
         * a bit odd in implementation:
         * function returns number of new goal that came in when applying
         * op to source; needed for Goal Added Deletion Heuristic
         *
         *
         * rather naive axiom treatment: in the new state, all axiom-added fts
         * are made false, all axiom-deleted are made true;
         * then the op effects are executed;
         * then iteratively all axioms are applied until no more changes occur.
         */
        bool first_call_result_to_dest = true;
        bool[] in_source, in_dest, in_del, true_ef;
        int[] del;
        int num_del;
        int result_to_dest(FFState dest, FFState source, int op)

        {


            int i, j, ef;
            int r = -1;

            if (first_call_result_to_dest)
            {
                in_source = new bool[FF.CF.gnum_ft_conn];// (bool*)calloc(, sizeof(bool));
                in_dest = new bool[FF.CF.gnum_ft_conn];// (bool*)calloc(, sizeof(bool));
                in_del = new bool[FF.CF.gnum_ft_conn];// (bool*)calloc(, sizeof(bool));
                true_ef = new bool[FF.CF.gnum_ef_conn];//(bool*)calloc(, sizeof(bool));
                del = new int[FF.CF.gnum_ft_conn];// (int*)calloc(, sizeof(int));
                for (i = 0; i < FF.CF.gnum_ft_conn; i++)
                {
                    in_source[i] = false;
                    in_dest[i] = false;
                    in_del[i] = false;
                }
                for (i = 0; i < FF.CF.gnum_ef_conn; i++)
                {
                    true_ef[i] = false;
                }
                first_call_result_to_dest = false;
            }

            /* setup true facts for effect cond evaluation
             */
            for (i = 0; i < source.num_F; i++)
            {
                in_source[source.F[i]] = true;
            }

            /* setup deleted facts
             */
            num_del = 0;
            for (i = 0; i < FF.CF.gop_conn[op].num_E; i++)
            {
                ef = FF.CF.gop_conn[op].E[i];
                for (j = 0; j < FF.CF.gef_conn[ef].num_PC; j++)
                {
                    if (!in_source[FF.CF.gef_conn[ef].PC[j]]) break;
                }
                if (j < FF.CF.gef_conn[ef].num_PC) continue;
                true_ef[i] = true;
                for (j = 0; j < FF.CF.gef_conn[ef].num_D; j++)
                {
                    if (in_del[FF.CF.gef_conn[ef].D[j]]) continue;
                    in_del[FF.CF.gef_conn[ef].D[j]] = true;
                    del[num_del++] = FF.CF.gef_conn[ef].D[j];
                }
            }

            /* put all non-deleted facts from source into dest.
             * need not check for put-in facts here,
             * as initial state is made doubles-free, and invariant keeps
             * true through the transition procedure
             */
            dest.num_F = 0;
            for (i = 0; i < source.num_F; i++)
            {
                if (in_del[source.F[i]])
                {
                    continue;
                }
                /* no axiom adds or dels
                 */
                if (FF.CF.gft_conn[source.F[i]].axiom_add ||
                 FF.CF.gft_conn[source.F[i]].axiom_del)
                {
                    continue;
                }
                dest.F[dest.num_F++] = source.F[i];
                in_dest[source.F[i]] = true;
            }

            /* now add all fullfilled effect adds to dest; 
             * each fact at most once!
             */
            for (i = 0; i < FF.CF.gop_conn[op].num_E; i++)
            {
                if (!true_ef[i]) continue;
                ef = FF.CF.gop_conn[op].E[i];
                for (j = 0; j < FF.CF.gef_conn[ef].num_A; j++)
                {
                    if (in_dest[FF.CF.gef_conn[ef].A[j]])
                    {
                        continue;
                    }
                    dest.F[dest.num_F++] = FF.CF.gef_conn[ef].A[j];
                    in_dest[FF.CF.gef_conn[ef].A[j]] = true;
                    if (FF.CF.gft_conn[FF.CF.gef_conn[ef].A[j]].is_global_goal)
                    {
                        r = FF.CF.gef_conn[ef].A[j];
                    }
                }
            }

            /* put axiom-dels in, apply axioms til fixpoint.
             */
            do_axiom_update(dest);

            /* unset infos
             */
            for (i = 0; i < source.num_F; i++)
            {
                in_source[source.F[i]] = false;
            }
            for (i = 0; i < dest.num_F; i++)
            {
                in_dest[dest.F[i]] = false;
            }
            for (i = 0; i < num_del; i++)
            {
                in_del[del[i]] = false;
            }
            for (i = 0; i < FF.CF.gop_conn[op].num_E; i++)
            {
                true_ef[i] = false;
            }

            if (gcmd_line.debug >= 2)
            {
                FFUtilities.Write("\n\n----------------------------------------------result: ");
                print_state(source);
                FFUtilities.Write("\n---- ");
                print_op_name(op);
                print_state(dest);
            }

            return r;

        }



        bool[] in_dest_do_axiom_update;
        bool first_call_do_axiom_update = true;
        public void do_axiom_update(FFState dest)

        {


            int i, j, k, ft, n;
            bool changes;

            if (first_call_do_axiom_update)
            {
                in_dest_do_axiom_update = new bool[FF.CF.gnum_ft_conn];// (bool*)calloc(, sizeof(bool));
                for (i = 0; i < FF.CF.gnum_ft_conn; i++)
                {
                    in_dest_do_axiom_update[i] = false;
                }
                first_call_do_axiom_update = false;
            }

            if (gcmd_line.debug >= 3)
            {
                FFUtilities.Write("\n\n----------------------------------------------entering axiom update");
            }

            for (i = 0; i < dest.num_F; i++)
            {
                in_dest_do_axiom_update[dest.F[i]] = true;
            }

            if (gcmd_line.debug >= 3)
            {
                FFUtilities.Write("\n\n----------------------------------------------dest prior axfp");
                print_state(dest);
            }

            /* now apply the axioms up to a fixpoint.
             */
            for (n = 1; n < FF.Planning.gnum_strata; n++)
            {
                if (gcmd_line.debug >= 3)
                {
                    FFUtilities.Write("\n\n-----------------------------------stratum %d", n);
                }

                changes = true;
                while (changes)
                {
                    changes = false;

                    if (gcmd_line.debug >= 3)
                    {
                        FFUtilities.Write("\n\n---------------------------new ax iteration");
                    }
                    FF.RLX.get_axA(dest);
                    for (i = 0; i < gnum_axA; i++)
                    {
                        /* DEBUG
                         */
                        if (!FF.CF.gop_conn[gaxA[i]].axiom)
                        {
                            FFUtilities.Write("\naxiom A no axiom??\n\n");
                            Exit(1);
                        }
                        if (FF.CF.gop_conn[gaxA[i]].stratum != n)
                        {
                            continue;
                        }
                        if (gcmd_line.debug >= 3)
                        {
                            FFUtilities.Write("\n----------------------------------apply axiom ");
                            print_op_name(gaxA[i]);
                        }
                        ft = FF.CF.gef_conn[FF.CF.gop_conn[gaxA[i]].E[0]].A[0];
                        if (in_dest_do_axiom_update[ft])
                        {
                            continue;
                        }
                        changes = true;
                        if (gcmd_line.debug >= 3)
                        {
                            FFUtilities.Write(" ADD! ");
                            print_ft_name(ft);
                        }
                        dest.F[dest.num_F++] = ft;
                        in_dest_do_axiom_update[ft] = true;

                        if (FF.CF.gef_conn[FF.CF.gop_conn[gaxA[i]].E[0]].num_D > 0)
                        {
                            ft = FF.CF.gef_conn[FF.CF.gop_conn[gaxA[i]].E[0]].D[0];
                            if (!in_dest_do_axiom_update[ft]) continue;
                            changes = true;
                            if (gcmd_line.debug >= 3)
                            {
                                FFUtilities.Write(" DEL! ");
                                print_ft_name(ft);
                            }

                            for (j = 0; j < dest.num_F; j++)
                            {
                                if (dest.F[j] == ft) break;
                            }
                            if (j == dest.num_F)
                            {
                                FFUtilities.Write("\naxiom-deleted fact not in dest??\n\n");
                                Exit(1);
                            }
                            for (k = j; k < dest.num_F - 1; k++)
                            {
                                dest.F[k] = dest.F[k + 1];
                            }
                            dest.num_F--;
                            in_dest_do_axiom_update[ft] = false;
                        }
                    }
                }
            }

            if (gcmd_line.debug >= 3)
            {
                FFUtilities.Write("\n\n----------------------------------------------dest after ax fp");
                print_state(dest);
            }

            for (i = 0; i < dest.num_F; i++)
            {
                in_dest_do_axiom_update[dest.F[i]] = false;
            }

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



        void copy_source_to_dest(FFState dest, FFState source)

        {

            int i, m;

            if (dest.max_F < source.num_F)
            {
                if (dest.F != null)
                {
                    //free(dest.F);
                }
                if (source.num_F + 50 > FF.CF.gnum_ft_conn)
                {
                    m = FF.CF.gnum_ft_conn;
                }
                else
                {
                    m = source.num_F + 50;
                }
                dest.F = new int[m];
                dest.max_F = m;
            }

            for (i = 0; i < source.num_F; i++)
            {
                dest.F[i] = source.F[i];
            }
            dest.num_F = source.num_F;

        }



        void print_state(FFState S)

        {

            int i;

            for (i = 0; i < S.num_F; i++)
            {
                FFUtilities.Write("\n");
                print_ft_name(S.F[i]);
            }

        }

    }
}
