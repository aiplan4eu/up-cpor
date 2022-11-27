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
using static CPORLib.FFCS.InstPre;


namespace CPORLib.FFCS
{
    public class Orderings
    {



        /* local globals
         */








        static int[] lch;
        static int lnum_ch;
        static bool[] lin_ch;

        static int[] lDcount;

        static bool[] lin;

        static bool[,] lm;









        /* main function
         */








        static void  compute_goal_agenda()

        {

            int i;
            int max = FF.CF.gnum_ef_conn > FF.CF.gnum_ft_conn ?
              FF.CF.gnum_ef_conn : FF.CF.gnum_ft_conn;

            /* initialization stuff
             */
            lch = new int[max];// new int[];//(max, sizeof(int));
            lin_ch = new bool[max]; //(bool*)calloc(max, sizeof(bool));
            for (i = 0; i < max; i++)
            {
                lin_ch[i] = false;
            }

            lDcount = new int[FF.CF.gnum_ft_conn];//new int[];//(, sizeof(int));
            for (i = 0; i < FF.CF.gnum_ft_conn; i++)
            {
                lDcount[i] = 0;
            }

            /* False sets
             */
            for (i = 0; i < FF.DP.ggoal_state.num_F; i++)
            {
                build_False_set(FF.DP.ggoal_state.F[i]);
            }

            /* heuristic reasonable orderings
             */
            detect_ordering_constraints();

            /* build orderings into goal agenda
             */
            build_goal_agenda();

        }










        /* false set computation for each goal
         */










        static void  build_False_set(int ft)

        {

            int i, j, k, count;
            int ef, ft_, ef_;

            lnum_ch = 0;

            count = 0;
            for (i = 0; i < FF.CF.gft_conn[ft].num_A; i++)
            {
                ef = FF.CF.gft_conn[ft].A[i];
                count++;
                for (j = 0; j < FF.CF.gef_conn[ef].num_D; j++)
                {
                    ft_ = FF.CF.gef_conn[ef].D[j];
                    lDcount[ft_]++;
                    if (!lin_ch[ft_])
                    {
                        lch[lnum_ch++] = ft_;
                        lin_ch[ft_] = true;
                    }
                }
                for (j = 0; j < FF.CF.gef_conn[ef].num_I; j++)
                {
                    ef_ = FF.CF.gef_conn[ef].I[j];
                    count++;
                    for (k = 0; k < FF.CF.gef_conn[ef_].num_D; k++)
                    {
                        ft_ = FF.CF.gef_conn[ef_].D[k];
                        lDcount[ft_]++;
                        if (!lin_ch[ft_])
                        {
                            lch[lnum_ch++] = ft_;
                            lin_ch[ft_] = true;
                        }
                    }
                }
            }

            /* only those that where deleted can be in False set
             *
             * DANGER: this relies on that the function is called only once
             *         for each fact ft
             */
            FF.CF.gft_conn[ft].False = new int[lnum_ch];// new int[];//(, sizeof(int));

            FF.CF.gft_conn[ft].num_False = 0;
            for (i = 0; i < lnum_ch; i++)
            {
                if (lDcount[lch[i]] == count)
                {
                    /* each adder deleted this fact
                     */
                    FF.CF.gft_conn[ft].False[FF.CF.gft_conn[ft].num_False++] = lch[i];
                }
            }

            /* undo Dcount and lch information now
             */
            for (i = 0; i < lnum_ch; i++)
            {
                lDcount[lch[i]] = 0;
                lin_ch[lch[i]] = false;
            }

            if (gcmd_line.display_info == 125)
            {
                FFUtilities.Write("\n\ncomputed False set of ");
                print_ft_name(ft);
                FFUtilities.Write(" as follows:");
                for (i = 0; i < FF.CF.gft_conn[ft].num_False; i++)
                {
                    FFUtilities.Write("\n");
                    print_ft_name(FF.CF.gft_conn[ft].False[i]);
                }
            }

        }










        /* look at pairs of goals and see if they are ordered
         * heuristically reasonable
         */











        static void  detect_ordering_constraints()

        {

            int i, j, n = FF.DP.ggoal_state.num_F;

            /* initialize usability array
             */
            lin = new bool[FF.CF.gnum_ef_conn];// (bool*)calloc(, sizeof(bool));
            for (i = 0; i < FF.CF.gnum_ef_conn; i++)
            {
                lin[i] = true;
            }

            /* initialize orderings matrix.
             *
             * m[i,j] == true gdw. goal[i] \leq_h goal[j]
             */
            lm = new bool[n, n];// (bool**)calloc(n, sizeof(bool*));
            
            for (i = 0; i < n; i++)
            {
                for (j = 0; j < n; j++)
                {
                    lm[i,j] = (i == j ? true : false);
                }
            }

            /* check each pair of goals i, j for heuristic
             * reasonable ordering.
             *
             * order of pairs due to speedup by marking
             * unusable efs for each as long as possible constant
             * goal i
             */
            for (i = 0; i < n - 1; i++)
            {
                setup_E(FF.DP.ggoal_state.F[i]);
                for (j = i + 1; j < n; j++)
                {
                    lm[j,i] = !possibly_achievable(FF.DP.ggoal_state.F[j]);
                    if (gcmd_line.display_info == 126 &&
                     lm[j,i])
                    {
                        FFUtilities.Write("\norderings: ");
                        print_ft_name(FF.DP.ggoal_state.F[j]);
                        FFUtilities.Write(" <= ");
                        print_ft_name(FF.DP.ggoal_state.F[i]);
                    }
                }
                unsetup_E(FF.DP.ggoal_state.F[i]);
            }
            for (i = n - 1; i > 0; i--)
            {
                setup_E(FF.DP.ggoal_state.F[i]);
                for (j = i - 1; j > -1; j--)
                {
                    lm[j,i] = !possibly_achievable(FF.DP.ggoal_state.F[j]);
                    if (gcmd_line.display_info == 126 &&
                     lm[j,i])
                    {
                        FFUtilities.Write("\norderings: ");
                        print_ft_name(FF.DP.ggoal_state.F[j]);
                        FFUtilities.Write(" <= ");
                        print_ft_name(FF.DP.ggoal_state.F[i]);
                    }
                }
                unsetup_E(FF.DP.ggoal_state.F[i]);
            }

        }



        static void  setup_E(int ft)

        {

            int i, j;
            int ef, ef_, ft_;

            lnum_ch = 0;

            /* efs that imply a delete ef to ft
             */
            for (i = 0; i < FF.CF.gft_conn[ft].num_D; i++)
            {
                ef = FF.CF.gft_conn[ft].D[i];
                if (!lin_ch[ef])
                {
                    lin[ef] = false;
                    lch[lnum_ch++] = ef;
                    lin_ch[ef] = true;
                }
                for (j = 0; j < FF.CF.gef_conn[ef].num_I; j++)
                {
                    ef_ = FF.CF.gef_conn[ef].I[j];
                    if (!lin_ch[ef_])
                    {
                        lin[ef_] = false;
                        lch[lnum_ch++] = ef_;
                        lin_ch[ef_] = true;
                    }
                }
            }

            /* efs that use False preconds
             */
            for (i = 0; i < FF.CF.gft_conn[ft].num_False; i++)
            {
                ft_ = FF.CF.gft_conn[ft].False[i];
                for (j = 0; j < FF.CF.gft_conn[ft_].num_PC; j++)
                {
                    ef = FF.CF.gft_conn[ft_].PC[j];
                    if (!lin_ch[ef])
                    {
                        lin[ef] = false;
                        lch[lnum_ch++] = ef;
                        lin_ch[ef] = true;
                    }
                }
            }

        }



        static void  unsetup_E(int ft)

        {

            int i;

            for (i = 0; i < lnum_ch; i++)
            {
                lin[lch[i]] = true;
                lin_ch[lch[i]] = false;
            }

        }



        static bool possibly_achievable(int ft)

        {

            int i, j, k;
            int ef, ft_;

            for (i = 0; i < FF.CF.gft_conn[ft].num_A; i++)
            {
                ef = FF.CF.gft_conn[ft].A[i];
                if (!lin[ef])
                {
                    continue;
                }
                for (j = 0; j < FF.CF.gef_conn[ef].num_PC; j++)
                {
                    ft_ = FF.CF.gef_conn[ef].PC[j];
                    for (k = 0; k < FF.CF.gft_conn[ft_].num_A; k++)
                    {
                        if (lin[FF.CF.gft_conn[ft_].A[k]])
                        {
                            break;
                        }
                    }
                    if (k == FF.CF.gft_conn[ft_].num_A)
                    {
                        break;
                    }
                }
                if (j < FF.CF.gef_conn[ef].num_PC)
                {
                    continue;
                }
                return true;
            }

            return false;

        }









        /* take a matrix of goal orderings and build it into
         * the goal agenda
         */












        static void  build_goal_agenda()

        {

            int i, j, k, n = FF.DP.ggoal_state.num_F, start, entry;
            int[] degree;
            int[] hits;
            int[] slot;

            degree = new int[n];//(n, sizeof(int));
            hits = new int[n];//(n, sizeof(int));
            slot = new int[n];//(n, sizeof(int));
            for (i = 0; i < n; i++)
            {
                degree[i] = 0;
                hits[i] = 0;
            }

            /* compute transitive closure on orderings matrix
             */
            for (j = 0; j < n; j++)
            {
                for (i = 0; i < n; i++)
                {
                    if (lm[i,j])
                    {
                        for (k = 0; k < n; k++)
                        {
                            if (lm[j,k])
                            {
                                lm[i,k] = true;
                            }
                        }
                    }
                }
            }

            /* count in - and outgoing edges, know those
             * goals that are not connected at all
             */
            for (i = 0; i < n; i++)
            {
                for (j = 0; j < n; j++)
                {
                    if (i != j && lm[i,j])
                    {
                        degree[i]--;
                        degree[j]++;
                        hits[i]++;
                        hits[j]++;
                    }
                }
            }

            /* order goals with increasing degree, disconnected
             * at the very end.
             */
            for (i = 0; i < n; i++)
            {
                if (hits[i] == 0)
                {
                    slot[i] = i;
                    continue;
                }
                for (j = 0; j < i; j++)
                {
                    if (degree[i] < degree[slot[j]] ||
                     hits[slot[j]] == 0)
                    {
                        break;
                    }
                }
                for (k = i - 1; k >= j; k--)
                {
                    slot[k + 1] = slot[k];
                }
                slot[j] = i;
            }

            /* sweep over and collect goal agenda
             */
            FF.Search.ggoal_agenda = new FFState[n];// (State*)calloc(n, sizeof(State));
            for (i = 0; i < n; i++)
            {
                FF.Search.ggoal_agenda[i] = new FFState(FF.CF.gnum_ft_conn);
                FF.Search.ggoal_agenda[i].max_F = FF.CF.gnum_ft_conn;
            }

            start = 0;
            entry = 0;
            for (i = 1; i < n; i++)
            {
                if ((degree[slot[i]] != degree[slot[i - 1]]) ||
                 (hits[slot[i]] == 0 && hits[slot[i - 1]] != 0))
                {
                    FF.Search.ggoal_agenda[entry].num_F = 0;
                    for (j = start; j < i; j++)
                    {
                        FF.Search.ggoal_agenda[entry].F[FF.Search.ggoal_agenda[entry].num_F++] =
                          FF.DP.ggoal_state.F[slot[j]];
                    }
                    entry++;
                    start = i;
                }
            }
            FF.Search.ggoal_agenda[entry].num_F = 0;
            for (i = start; i < n; i++)
            {
                FF.Search.ggoal_agenda[entry].F[FF.Search.ggoal_agenda[entry].num_F++] =
                  FF.DP.ggoal_state.F[slot[i]];
            }
            entry++;
            FF.Search.gnum_goal_agenda = entry;

           //free(degree);
           //free(hits);
           //free(slot);

            if (gcmd_line.display_info == 127)
            {
                FFUtilities.Write("\ngoal agenda is:\n");
                for (i = 0; i < FF.Search.gnum_goal_agenda; i++)
                {
                    if (i == 0)
                    {
                        FFUtilities.Write("\nentry %3d: ", i);
                    }
                    else
                    {
                        FFUtilities.Write("\n      %3d: ", i);
                    }
                    for (j = 0; j < FF.Search.ggoal_agenda[i].num_F; j++)
                    {
                        print_ft_name(FF.Search.ggoal_agenda[i].F[j]);
                        if (j < FF.Search.ggoal_agenda[i].num_F - 1)
                        {
                            FFUtilities.Write("\n           ");
                        }
                    }
                }
            }

        }


    }
}
