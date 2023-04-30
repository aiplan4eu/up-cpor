using System;
using System.Collections.Generic;


using static CPORLib.FFCS.Output;
using static CPORLib.FFCS.Constants;
using static CPORLib.FFCS.InstFinal;
using static CPORLib.FFCS.FFUtilities;
using CPORLib.PlanningModel;
using CPORLib.Algorithms;
using System.IO;
using CPORLib.Parsing;
using Microsoft.SolverFoundation.Services;

namespace CPORLib.FFCS
{
    public class FF : Planner
    {

        public static DomainProperties DP;
        public static Inertia Inertia;
        public static ConnectivityGraph CF;
        public static Parsing Parsing;
        public static Planning Planning;
        public static InstPre IP;
        public static Relax RLX;
        public static Search Search;

        public InstHard IH;
        public InstEasy IE;
        public Parse Parse;


        public int main(int argc, string[] argv)
        {
            DP = new DomainProperties();
            Inertia = new Inertia();
            CF = new ConnectivityGraph();

            /* resulting name for ops file
             */
            string ops_file = "";
            /* same for fct file 
             */
            string fct_file = "";

            //struct tms start, end;

            int i, j;
            bool found_plan;


            if (false)
            {
                /* command line treatment
                 */
                if (argc == 1 || (argc == 2 && argv[1] == "?"))
                {
                    ff_usage();
                    Exit(1);
                }
                /*
                if (!process_command_line(argc, argv))
                {
                    ff_usage();
                    Exit(1);
                }
                */

                /* make file names
                 */

                /* one input name missing
                 */
                if (gcmd_line.ops_file_name == null ||
                     gcmd_line.fct_file_name == null)
                {
                    FFUtilities.Write("\nff: two input files needed\n\n");
                    ff_usage();
                    Exit(1);
                }
                /* add path info, complete file names will be stored in
                 * ops_file and fct_file 
                 */
                ops_file = gcmd_line.path + gcmd_line.ops_file_name;
                fct_file = gcmd_line.path + gcmd_line.fct_file_name;


                /* parse the input files
                 */

                /* start parse & instantiation timing
                 */
                /* domain file (ops)
                 */
                if (gcmd_line.display_info >= 1)
                {
                    FFUtilities.Write("\nff: parsing domain file");
                }
                /* it is important for the pddl language to define the domain before 
                 * reading the problem 
                 */
                //load_ops_file(ops_file); flex
                /* problem file (facts)
                 */
                if (gcmd_line.display_info >= 1)
                {
                    FFUtilities.Write(" ... done.\nff: parsing problem file");
                }
                //load_fct_file(fct_file); flex
                if (gcmd_line.display_info >= 1)
                {
                    FFUtilities.Write(" ... done.\n\n");
                }
            }

            /* This is needed to get all types.
             */
            Parse.build_orig_constant_list();

            /* last step of parsing: see if it's an ADL domain!
             */
            if (!Parse.make_adl_domain())
            {
                FFUtilities.Write("\nff: this is not an ADL problem!");
                FFUtilities.Write("\n    can't be handled by this version.\n\n");
                Exit(1);
            }

            FF.Planning.gnum_strata = 1;
            /* now instantiate operators;
             */


            /**************************
             * first do PREPROCESSING * 
             **************************/


            /* start by collecting all strings and thereby encoding 
             * the domain in integers.
             */
            FF.IP.encode_domain_in_integers();

            /* inertia preprocessing, first step:
             *   - collect inertia information
             *   - split initial state into
             *        _ arrays for individual predicates
             *        - arrays for all static relations
             *        - array containing non - static relations
             */
            FF.IP.do_inertia_preprocessing_step_1();

            /* normalize all PL1 formulae in domain description:
             * (goal, preconds and effect conditions)
             *   - simplify formula
             *   - expand quantifiers
             *   - NOTs down
             */
            FF.IP.normalize_all_wffs();

            /* translate negative preconds: introduce symmetric new predicate
             * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
             */
            FF.IP.translate_negative_preconds();

            /* split domain in easy (disjunction of conjunctive preconds)
             * and hard (non FF.IP.dnf preconds) part, to apply 
             * different instantiation algorithms
             */
            FF.IP.split_domain();


            /***********************************************
             * PREPROCESSING FINISHED                      *
             *                                             *
             * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
             ***********************************************/

            IE.build_easy_action_templates();
            IH.build_hard_action_templates();

            //times( &end );
            //TIME( gtempl_time );

            //times( &start );

            /* perform reachability analysis in terms of relaxed 
             * fixpoint
             */
            perform_reachability_analysis();

            //times( &end );
            //TIME( greach_time );

            //times( &start );

            /* collect the relevant facts and build final domain
             * and problem representations.
             */
            collect_relevant_facts();

            //times( &end );
            //TIME( grelev_time );

            //times( &start );

            /* now build globally accessable connectivity graph
             */
            build_connectivity_graph();

            //times( &end );
            //TIME( gconn_time );

            /***********************************************************
             * we are finally throuFF.Search.gH with preprocessing and can worry *
             * bout finding a plan instead.                            *
             ***********************************************************/

            //times( &start );

            FF.RLX.initialize_relax();
            i = 0;
            while (i < FF.DP.ginitial_state.num_F)
            {
                if (!FF.CF.gft_conn[FF.DP.ginitial_state.F[i]].axiom_add &&
                 !FF.CF.gft_conn[FF.DP.ginitial_state.F[i]].axiom_del)
                {
                    i++;
                    continue;
                }
                for (j = i; j < FF.DP.ginitial_state.num_F - 1; j++)
                {
                    FF.DP.ginitial_state.F[j] = FF.DP.ginitial_state.F[j + 1];
                }
                FF.DP.ginitial_state.num_F--;
            }
            Search.do_axiom_update(FF.DP.ginitial_state);

            /* make space in plan states info, and relax
             */
            for (i = 0; i < MAX_PLAN_LENGTH + 1; i++)
            {
                FF.Planning.gplan_states[i] = new FFState(FF.CF.gnum_ft_conn);
                FF.Planning.gplan_states[i].max_F = FF.CF.gnum_ft_conn;
            }

            found_plan = Search.do_enforced_hill_climbing(FF.DP.ginitial_state, FF.DP.ggoal_state);

            if (!found_plan)
            {
                FFUtilities.Write("\n\nEnforced Hill-climbing failed !");
                FFUtilities.Write("\nswitching to Best-first Search now.\n");
                found_plan = Search.do_best_first_search();
            }

            //times( &end );
            //TIME( gsearch_time );

            if (found_plan)
            {
                print_plan();
            }

            output_planner_info();

            FFUtilities.Write("\n\n");
            return 0;

        }


        public FF(PlanningModel.Domain d, Problem p) : base(d, p)
        {
            Init();
        }

        public FF(MemoryStream msModel) : base(null, null)
        {
            /*
            FileStream swDomain = new FileStream(@"C:\\temp\\FF-X\\blocks\Kd.pddl", FileMode.Create);
            msModel.WriteTo(swDomain);
            //swDomain.Write(m_dDomain.ToString());
            swDomain.Close();
            StreamWriter swProblem = new StreamWriter(@"C:\\temp\\FF-X\\blocks\Kp.pddl");
            swProblem.Write(m_pProblem.ToString());
            swProblem.Close();
            */
            Parser p = new Parser();
            msModel.Position = 0;
            p.ParseDomainAndProblem(msModel, out m_dDomain, out m_pProblem);

            /*
            StreamWriter swOut = new StreamWriter("debug1.log");
            swOut.WriteLine(m_dDomain);
            swOut.WriteLine();
            swOut.WriteLine(m_pProblem);
            swOut.Close();
            */

            Init();
        }

        private void Init()
        {
            EfficientArrayMemory.Reset();


            DP = new DomainProperties();
            Inertia = new Inertia();
            CF = new ConnectivityGraph();
            Parsing = new Parsing();
            Search = new Search();
            Planning = new Planning();
            IP = new InstPre();
            IH = new InstHard();
            IE = new InstEasy();
            Parse = new Parse();
            RLX = new Relax();

            InputConverter cv = new InputConverter();
            cv.Process(m_dDomain, m_pProblem);

            //BFSSolver bfs = new BFSSolver();
            //bfs.ManualSolve(m_pProblem, m_dDomain, false);

        }

        public List<string> Plan()
        {
            
            int i, j;
            bool found_plan;


            /* This is needed to get all types.
             */
            Parse.build_orig_constant_list();

            /* last step of parsing: see if it's an ADL domain!
             */
            if (!Parse.make_adl_domain())
            {
                FFUtilities.Write("\nff: this is not an ADL problem!");
                FFUtilities.Write("\n    can't be handled by this version.\n\n");
                return null;
            }

            FF.Planning.gnum_strata = 1;
            /* now instantiate operators;
             */


            /**************************
             * first do PREPROCESSING * 
             **************************/


            /* start by collecting all strings and thereby encoding 
             * the domain in integers.
             */
            FF.IP.encode_domain_in_integers();

            /* inertia preprocessing, first step:
             *   - collect inertia information
             *   - split initial state into
             *        _ arrays for individual predicates
             *        - arrays for all static relations
             *        - array containing non - static relations
             */
            FF.IP.do_inertia_preprocessing_step_1();

            /* normalize all PL1 formulae in domain description:
             * (goal, preconds and effect conditions)
             *   - simplify formula
             *   - expand quantifiers
             *   - NOTs down
             */
            FF.IP.normalize_all_wffs();

            /* translate negative preconds: introduce symmetric new predicate
             * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
             */
            FF.IP.translate_negative_preconds();

            /* split domain in easy (disjunction of conjunctive preconds)
             * and hard (non FF.IP.dnf preconds) part, to apply 
             * different instantiation algorithms
             */
            FF.IP.split_domain();


            /***********************************************
             * PREPROCESSING FINISHED                      *
             *                                             *
             * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
             ***********************************************/

            IE.build_easy_action_templates();
            IH.build_hard_action_templates();

            /* perform reachability analysis in terms of relaxed 
             * fixpoint
             */
            perform_reachability_analysis();

            //times( &end );
            //TIME( greach_time );

            //times( &start );

            /* collect the relevant facts and build final domain
             * and problem representations.
             */
            collect_relevant_facts();


            /* now build globally accessable connectivity graph
             */
            build_connectivity_graph();

            /***********************************************************
             * we are finally throuFF.Search.gH with preprocessing and can worry *
             * bout finding a plan instead.                            *
             ***********************************************************/


            FF.RLX.initialize_relax();
            i = 0;
            while (i < FF.DP.ginitial_state.num_F)
            {
                if (!FF.CF.gft_conn[FF.DP.ginitial_state.F[i]].axiom_add &&
                 !FF.CF.gft_conn[FF.DP.ginitial_state.F[i]].axiom_del)
                {
                    i++;
                    continue;
                }
                for (j = i; j < FF.DP.ginitial_state.num_F - 1; j++)
                {
                    FF.DP.ginitial_state.F[j] = FF.DP.ginitial_state.F[j + 1];
                }
                FF.DP.ginitial_state.num_F--;
            }
            Search.do_axiom_update(FF.DP.ginitial_state);

            /* make space in plan states info, and relax
             */
            for (i = 0; i < MAX_PLAN_LENGTH + 1; i++)
            {
                FF.Planning.gplan_states[i] = new FFState(FF.CF.gnum_ft_conn);
                FF.Planning.gplan_states[i].max_F = FF.CF.gnum_ft_conn;
            }

            found_plan = Search.do_enforced_hill_climbing(FF.DP.ginitial_state, FF.DP.ggoal_state);

            if (!found_plan)
            {
                FFUtilities.Write("\n\nEnforced Hill-climbing failed !");
                FFUtilities.Write("\nswitching to Best-first Search now.\n");
                found_plan = Search.do_best_first_search();
            }

            List<string> lPlan = null;
            if (found_plan)
            {
                lPlan = GetPlan();
            }
            else
            {
                BFSSolver bfs = new BFSSolver();
                var p = bfs.ManualSolve(m_pProblem, m_dDomain, false);
            }

            output_planner_info();

            FFUtilities.Write("\n\n");

            return lPlan;

        }


        List<string> GetPlan()

        {
            List<string> lPlan = new List<string>();
            int i;

            for (i = 0; i < FF.Planning.gnum_plan_ops; i++)
            {
                FFUtilities.Write(i + ":");
                int index = FF.Planning.gplan_ops[i];
                Action a = FF.CF.gop_conn[index].action;
                lPlan.Add(a.name);
            }
            return lPlan;
        }


        void print_plan()

        {

            int i;

            FFUtilities.Write("\n\nff: found legal plan as follows");
            FFUtilities.Write("\n\nstep ");
            for (i = 0; i < FF.Planning.gnum_plan_ops; i++)
            {
                FFUtilities.Write(i + ":");
                print_op_name(FF.Planning.gplan_ops[i]);
                FFUtilities.Write("\n     ");
            }

        }


        void output_planner_info()

        {


            FFUtilities.Write("\n\ntime spent: instantiating %d easy, %d hard action templates",
                 FF.DP.gnum_easy_templates, FF.DP.gnum_hard_mixed_operators);
            FFUtilities.Write("\n           reachability analysis, yielding %d facts and %d actions",
                 FF.DP.gnum_pp_facts, FF.DP.gnum_actions);
            FFUtilities.Write("\n             creating final representation with %d relevant facts",
                 FF.DP.gnum_relevant_facts);
            FFUtilities.Write("\n             building connectivity graph"
                );
            FFUtilities.Write("\n            searching, evaluating %d states, to a max depth of %d",
                 FF.Search.gevaluated_states, FF.Search.gmax_search_depth);
            

            FFUtilities.Write("\n\n");

            
        



        }



        void print_official_op_name(int index)

        {

            int i;
            Action a = FF.CF.gop_conn[index].action;

            if (a.norm_operator != null ||
                 a.pseudo_action != null)
            {
                FFUtilities.Write( "(%s", a.name);
                for (i = 0; i < a.num_name_vars; i++)
                {
                    FFUtilities.Write(" %s", FF.DP.gconstants[a.name_inst_table[i]]);
                }
                FFUtilities.Write( ")");
            }

        }



        void ff_usage()

        {

            FFUtilities.Write("\nusage of ff:\n");

            FFUtilities.Write("\nOPTIONS   DESCRIPTIONS\n\n");
            FFUtilities.Write("-p <str>    path for operator and fact file\n");
            FFUtilities.Write("-o <str>    operator file name\n");
            FFUtilities.Write("-f <str>    fact file name\n\n");
            FFUtilities.Write("-i <num>    run-time information level( preset: 1 )\n");
            FFUtilities.Write("      0     only times\n");
            FFUtilities.Write("      1     problem name, planning process infos\n");
            FFUtilities.Write("    101     parsed problem data\n");
            FFUtilities.Write("    102     cleaned up ADL problem\n");
            FFUtilities.Write("    103     collected string tables\n");
            FFUtilities.Write("    104     encoded domain\n");
            FFUtilities.Write("    105     predicates inertia info\n");
            FFUtilities.Write("    106     splitted initial state\n");
            FFUtilities.Write("    107     domain with Wff s normalized\n");
            FFUtilities.Write("    108     domain with NOT conds translated\n");
            FFUtilities.Write("    109     splitted domain\n");
            FFUtilities.Write("    110     cleaned up easy domain\n");
            FFUtilities.Write("    111     unaries encoded easy domain\n");
            FFUtilities.Write("    112     effects multiplied easy domain\n");
            FFUtilities.Write("    113     inertia removed easy domain\n");
            FFUtilities.Write("    114     easy action templates\n");
            FFUtilities.Write("    115     cleaned up hard domain representation\n");
            FFUtilities.Write("    116     mixed hard domain representation\n");
            FFUtilities.Write("    117     final hard domain representation\n");
            FFUtilities.Write("    118     reachability analysis results\n");
            FFUtilities.Write("    119     facts selected as relevant\n");
            FFUtilities.Write("    120     final domain and problem representations\n");
            FFUtilities.Write("    121     connectivity graph\n");
            FFUtilities.Write("    122     fixpoint result on each evaluated state\n");
            FFUtilities.Write("    123     1P extracted on each evaluated state\n");
            FFUtilities.Write("    124     H set collected for each evaluated state\n");
            FFUtilities.Write("    125     False sets of goals <GAM>\n");
            FFUtilities.Write("    126     detected ordering constraints leq_h <GAM>\n");
            FFUtilities.Write("    127     the Goal Agenda <GAM>\n");



            /*   Utilities.Write("    109     reachability analysis results\n"); */
            /*   Utilities.Write("    110     final domain representation\n"); */
            /*   Utilities.Write("    111     connectivity graph\n"); */
            /*   Utilities.Write("    112     False sets of goals <GAM>\n"); */
            /*   Utilities.Write("    113     detected ordering constraints leq_h <GAM>\n"); */
            /*   Utilities.Write("    114     the Goal Agenda <GAM>\n"); */
            /*   Utilities.Write("    115     fixpoint result on each evaluated state <1Ph>\n"); */
            /*   Utilities.Write("    116     1P extracted on each evaluated state <1Ph>\n"); */
            /*   Utilities.Write("    117     H set collected for each evaluated state <1Ph>\n"); */

            FFUtilities.Write("\n-d <num>    switch on debugging\n\n");

        }

        public override List<string> Plan(PlanningModel.State s)
        {
            throw new NotImplementedException();
        }

        public static void ClearEfficientMemory()
        {
            EfficientArrayMemory.Clear();
        }
    }
}
