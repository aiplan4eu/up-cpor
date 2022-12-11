using CPORLib.Algorithms;
using Microsoft.VisualBasic;
using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{
    public class Constants
    {

        public static int MAX_CONSTANTS = 20000;
        public static int MAX_PREDICATES = 50;
        public static int MAX_TYPES = 50;
        public static int MAX_ARITY = 5;
        public static int MAX_VARS = 15;


        public static int MAX_TYPE = 20000;


        public static  int MAX_OPERATORS = 50;


        /* in DNF: AND with OR - sons - collect 'hitting set':
         * one son of each OR node. 
         *
         * this here is initial max number of such son s that can be collected
         * (grows dynamically, if required)
         */
        public static int MAX_HITTING_SET_DEFAULT = 1000;


        public static  int MAX_TYPE_INTERSECTIONS = 10;


        public static  int MAX_RELEVANT_FACTS = 100000;


        public static int MAX_PLAN_LENGTH = 2000;



        /* marks border between connected items 
         */
        public static string CONNECTOR = "~";


        /* first size of goals_at array in 1P extraction
         */
        public static int RELAXED_STEPS_DEFAULT = 25;


        /* size of hash table for repeated states checking
         * during EHC breadth first search
         */
        public static int EHC_HASH_SIZE = 8192;
        public static int EHC_HASH_BITS = 8191;


        /* size of hash table for repeated states checking
         * in plan construction
         */
        public static int PLAN_HASH_SIZE = 1024;
        public static int PLAN_HASH_BITS = 1023;


        /* size of hash table for repeated states checking
         * during BFS search
         */
        public static int BFS_HASH_SIZE = 65536;
        public static int BFS_HASH_BITS = 65535;


        /* cut random values of facts off modulo this value,
         * to make state sums fit into a single integer
         */
        public static int BIG_INT = 1500000;

        /* various defines used in parsing
 */
        public static string HIDDEN_STR = "#";
        public static string AXIOM_STR = "AXIOM";
        public static string NAME_STR = "name";
        public static string VARIABLE_STR = "variable";
        public static string STANDARD_TYPE = "OBJECT";
        public static string EITHER_STR = "EITHER";

        /* not a real 'code' define; used in relax and search to encode
 * infinite level number / plan length
 */
        public static int INFINITY = -1;
    }





    public class FFUtilities
    {
        public static void strcpy(ref string s1, ref string s2)
        {
            s1 = s2;
        }

        public static int ENCODE_VAR(int val)
        {
            return (val * (-1)) - 1;
        }
        public static int DECODE_VAR(int val)
        {
            return (val + 1) * (-1);
        }
//public static int  ENCODE_VAR( val ) (val * (-1)) - 1
//public static int  DECODE_VAR( val ) (val + 1) * (-1)

        public static int GET_CONSTANT(int val, InstTable pointer)
        {
            return (val >= 0) ? val : pointer.inst_table[DECODE_VAR(val)];
        }
        //public static int  GET_CONSTANT( val, pointer ) ( val >= 0 ) ? val : pointer.inst_table[DECODE_VAR( val )]

        static Random rnd = new Random();
        public static int random(int max)
        {
            return rnd.Next(max);
        }

        public static void Exit(int iCode)
        {
            //System.Environment.Exit(iCode);
            throw new Exception();
        }

        public static bool Verbose = true;


        public static string Format(string s, params object[] list)
        {
            string sIn = s;
            string sOut = "";
            int i = 0;
            while (s != "")
            {
                int idx = s.IndexOf("%");
                if (idx >= 0)
                {
                    string sPrefix = s.Substring(0, idx);
                    string sSuffix = s.Substring(idx + 2);
                    sOut += sPrefix + list[i];
                    i++;
                    s = sSuffix;
                }
                else
                {
                    sOut += s;
                    s = "";
                }
            }
            return sOut;
        }

        public static void Write(string s)
        {
            CPORPlanner.TraceListener.Write(s);


            if (Verbose)
                Console.Write(s);
        }
        public static void Write(string s, params object[] list)
        {
            string sRevised = Format(s, list);

            CPORPlanner.TraceListener.Write(sRevised);


            if (Verbose)
            {
                Console.Write(sRevised);
            }
        }

        public static void WriteLine(string s = "")
        {
            CPORPlanner.TraceListener.WriteLine(s);


            if (Verbose)
                Console.WriteLine(s);
        }

        /*
        public static T MakeList<T>(List<T> l)  where SetNext(T t)
        {
            if (l.Count > 0)
            {
                for (int i = 0; i < l.Count - 1; i++)
                {
                    l[i].SetNext(l[i + 1]);
                    l[i].next = l[i + 1];
                    l[i + 1].previous = l[i];
                }
                return l[0];
            }
            return default(T);
        }
        */
    }

    public class gcmd_line
    {
        public static int display_info;
        public static int debug;
        public static string path;
        public static string ops_file_name;
        public static string fct_file_name;
    }


    public class Link<T>
    {
        public static implicit operator T(Link<T> l)
        {
            if (l is T t)
                return t;
            return default(T);
        }

        public T next;
        public T previous;
    }

    /* A list of strings
     */
    public class TokenList : Link<TokenList>
    {

        public TokenList(string s = null)
        {
            item = s;
        }

        public TokenList(TokenList tl)
        {
            item = tl.item;
            if (tl.next != null)
                next = new TokenList(tl.next);
        }

        public string item;
        //public TokenList next;

        public override string ToString()
        {
            if (next == null)
                return item;
            else
            {
                string s = next.ToString();
                return item + " " + s;
            }
        }
    }




    /* list of string lists
     */
    public class FactList
    {

        public TokenList item;
        public FactList next;

    }



    /* structure to store  typed-list-of <name>/<variable>,
     * as they are declared in PDDL files
     */
    public class TypedList
    {

        public string name;

        /* each item in this list is the name of a type which
         * our type is the union of (EITHER - types ...)
         *
         * usually, this will default to a single-item TokenList.
         */
        public TokenList type;
        /* after first sweep, this will contain the number in type table
         */
        public int n;

        public TypedList next;


        public TypedList(string sName, string sType)
        {
            name = sName;
            type = new TokenList();
            type.item = sType;
        }
        public TypedList(string sName)
        {
            name = sName;   
        }
        public TypedList()
        {

        }
    }




    /* only needed to parse in the predicates and their arg
     * definitions
     */
    public class TypedListList : Link<TypedListList>
    {
        public string predicate;

        public TypedList args;

        //public TypedListList next;

    }




    /* This type indicates whether a node in the pddl tree stands for
     * an atomic expression, a junctor or a quantor. 
     */
    public enum Connective
    {
        TRU,
        FAL,
        ATOM,
        NOT,
        AND,
        OR,
        ALL,
        EX,
        WHEN
    }




    /*
     * This is a node in the tree to parse PDDL files
     */
    public class PlNode
    {

        /* type of the node
         */
        public Connective connective;

        /* only for parsing: the var args in quantifiers
         */
        public TypedList parse_vars;

        /* AND, OR, NOT, WHEN => NULL
         * ALL, EX            => the quantified variable with its type
         * ATOM               => the atom as predicate.param1.param2....
         */
        public TokenList atom;

        /* (a) for AND, OR this is the list of sons(a AND b AND c...),
         * (b) for the rest this is the son, e.g. a subtree that is negated
         * (c) for WHEN, the first son is the condition and the next son
         * is the effect
         */
        public PlNode sons;

        /* if you have a list of sons, they are connected by next
         */
        public PlNode next;

        public PlNode(Connective c)
        {
            connective = c;
        }

        public void AddSon(PlNode son)
        {
            if (sons == null)
                sons = son;
            else
            {
                PlNode curr = sons;
                while(curr.next != null)
                {
                    curr = curr.next;
                }
                curr.next = son;
            }
        }

        public override string ToString()
        {
            string s = "(";
            if (connective == Connective.ATOM)
            {
                TokenList tl = atom;
                while (tl != null)
                {
                    s += tl.item + " ";
                    tl = tl.next;
                }
            }
            else
                throw new NotImplementedException();
                s += ")";
            return s;
        }
    }



    /*
     * This resembles an uninstantiated PDDL operator
     */
    public class PlOperator
    {

        public string name;
        public bool axiom;

        /* only important for PDDL where :VARS may be added to the param list
         * which must be hidden when writing the plan to an output file
         */
        private int RealParamsCount;
        public int number_of_real_params 
        { 
            get { return RealParamsCount; }
            set { RealParamsCount = value; }
        }

        /* the params, as they are declared in domain file
         */
        public TypedList parse_params;

        /* params is a list of variable/type pairs, such that:
         * factlist.item = [variable] . [type]
         */
        public FactList parameters;
        public PlNode preconds;
        public PlNode effects;

        public PlOperator next;

        public PlOperator(string sName)
        {
            name = sName;
        }

    }






    /***************** 
     * INSTANTIATION *
     *****************/


    /* helpers
     */

    //typedef public int TypeArray[MAX_TYPE_public intERSECTIONS];

    //typedef public int[] public int_popublic inter;




    /* first step structures: parsing & preprocessing
     */

    public class Fact
    {
        public int predicate;
        public Array<int> args = new Array<int>(Constants.MAX_ARITY);
        public Fact()
        {

        }
    }




    public class Facts
    {

        public Fact fact;

        public Facts next;

        public Facts()
        {
            fact = new Fact();
            next = null;
        }
    }




    public class WffNode
    {

       public  Connective connective;

        /* in ALL/EX s
         */
        public int var, var_type;
        public string var_name;

        /* in AND/OR s
         */
        public WffNode sons;
        /* sons are doubly connected linear list
         */
        public WffNode next;
        public WffNode prev;

        /* in ATOMs
         */
        public Fact fact;
        /* after translation: mark NOT-p s for efficiency
         */
        public int NOT_p;

        /* in ALL/EX/NOT
         */
        public WffNode son;

        /* for expansion speedup
         */
        public bool visited;

        public WffNode(Connective c)
        {
            connective = c;
            var = -1;
            var_type = -1;
            NOT_p = -1;
            visited = false;
            fact = new Fact();
        }

        /* no WHEN s here... use Pl Connectives anyway for simplicity
         */


    }




    public class Literal
    {

        public bool negated;

        public Fact fact;

        public Literal next;
        public Literal prev;

        public Literal()
        {
            fact = new Fact();
        }

    }




    public class Effect
    {

        public int num_vars;
        public int[] var_types = new int[Constants.MAX_VARS];
        public string[] var_names = new string[Constants.MAX_VARS];

        public WffNode conditions;

        public Literal effects;

        public Effect next;
        public Effect prev;

    }




    public class Operator
    {

        public string name;
        public string[] var_names = new string[Constants.MAX_VARS];

        public int number_of_real_params;
        public bool axiom;
        public int stratum;

        public int num_vars;
        public int[] var_types = new int[Constants.MAX_VARS];
        public bool[] removed = new bool[Constants.MAX_VARS];

        public WffNode preconds;

        public Effect effects;

        public bool hard;

        public Operator(string n, int norp)
        {
            int i;

            if (n != null)
            {
                name = n;
            }

            num_vars = 0;
            number_of_real_params = norp;

            for (i = 0; i < Constants.MAX_VARS; i++)
            {
                removed[i] = false;
            }
            preconds = null;
            effects = null;
            hard = true;
        }
    }





    /* second step: structures that keep already normalized
     * operators
     */


    public class InstTable
    {
        public Array<int> inst_table { get; private set; }

        public InstTable()
        {
            inst_table = new Array<int>(Constants.MAX_VARS);
        }
    }

    public class NormEffect : InstTable
    {

        public int num_vars; public int[] var_types = new int[Constants.MAX_VARS];
        

        public InitializedArray<Fact> conditions;
        public int num_conditions;

        public InitializedArray<Fact> adds;
        public int num_adds;
        public InitializedArray<Fact> dels;
        public int num_dels;

        public NormEffect prev;
        public NormEffect next;

        public NormEffect(Effect e)
        {
            int i;

            num_vars = e.num_vars;
            for (i = 0; i < e.num_vars; i++)
            {
                var_types[i] = e.var_types[i];
                inst_table[i] = -1;
            }

            conditions = null;
            num_conditions = 0;

            adds = null;
            num_adds = 0;
            dels = null;
            num_dels = 0;

            next = null;
            prev = null;
        }

        public NormEffect(NormEffect e)
        {
            int i, j, a;

            num_vars = 0;

            conditions = new InitializedArray<Fact>(e.num_conditions);
            num_conditions = e.num_conditions;
            for (i = 0; i < e.num_conditions; i++)
            {
                conditions[i].predicate = e.conditions[i].predicate;
                a = (e.conditions[i].predicate < 0) ? 2 : FF.DP.garity[e.conditions[i].predicate];
                for (j = 0; j < a; j++)
                {
                    conditions[i].args[j] = e.conditions[i].args[j];
                }
            }

            adds = new InitializedArray<Fact>(e.num_adds);
            num_adds = e.num_adds;
            for (i = 0; i < e.num_adds; i++)
            {
                adds[i].predicate = e.adds[i].predicate;
                for (j = 0; j < FF.DP.garity[e.adds[i].predicate]; j++)
                {
                    adds[i].args[j] = e.adds[i].args[j];
                }
            }
            dels = new InitializedArray<Fact>(e.num_dels);
            num_dels = e.num_dels;
            for (i = 0; i < e.num_dels; i++)
            {
                dels[i].predicate = e.dels[i].predicate;
                for (j = 0; j < FF.DP.garity[e.dels[i].predicate]; j++)
                {
                    dels[i].args[j] = e.dels[i].args[j];
                }
            }

            next = null;
            prev = null;
        }
    }




    public class NormOperator : InstTable
    {

        public Operator action_operator;

        public int num_vars; 
        public int[] var_types = new int[Constants.MAX_VARS];

        public int[] removed_vars = new int[Constants.MAX_VARS], type_removed_vars = new int[Constants.MAX_VARS];
        public int num_removed_vars;

        public InitializedArray<Fact> preconds;
        public int num_preconds;

        public NormEffect effects;

        public bool Out;

        public NormOperator(Operator op)
        {
            int i;

            action_operator = op;

            num_vars = op.num_vars;
            for (i = 0; i < op.num_vars; i++)
            {
                var_types[i] = op.var_types[i];
                inst_table[i] = -1;
            }
            num_removed_vars = 0;

            preconds = null;
            num_preconds = 0;

            effects = null;

           
        }
    }

    public class TypeArray
    {
        public int this[int i]
        {
            get { return Array[i]; }
            set { Array[i] = value; }
        }
        int[] Array = new int[Constants.MAX_TYPE_INTERSECTIONS];
    }




    /* minimal info for a fully instantiated easy operator;
     * yields one action when expanded
     */
    public class EasyTemplate : InstTable
    {

        public NormOperator op;


        public EasyTemplate prev;
        public EasyTemplate next;

        public EasyTemplate(NormOperator lo)
        {
            op = lo;
            prev = null;
            next = null;
        }
    }







    /* structures for hard ops
     */





    /* public intermediate step: structure for keeping hard ops
     * with normalized precondition, but arbitrary
     * effect conditions
     */
    public class MixedOperator : InstTable
    {

        public Operator action_operator;



        public InitializedArray<Fact> preconds;
        public int num_preconds;


        public Effect effects;

        public MixedOperator next;

        public MixedOperator(Operator op)
        {
            action_operator = op;
            num_preconds = 0;
        }
    }






    /* last hard step: everything is action - like, except that
     * facts are not yet public integer coded
     */

    public class PseudoActionEffect
    {

        public InitializedArray<Fact> conditions;
        public int num_conditions;

        public InitializedArray<Fact> adds;
        public int num_adds;
        public InitializedArray<Fact> dels;
        public int num_dels;

        public PseudoActionEffect next;

    }




    public class PseudoAction : InstTable
    {

        public Operator action_operator;



        public Fact[] preconds;
        public int num_preconds;

        public PseudoActionEffect effects;
        public int num_effects;

        public PseudoAction(MixedOperator op)
        {
            action_operator = op.action_operator;
            for (int i = 0; i < op.action_operator.num_vars; i++)
            {
               inst_table[i] = op.inst_table[i];
            }
            preconds = op.preconds;
            num_preconds = op.num_preconds;

            effects = null;
            num_effects = 0;
               
        }
    }





    /* final domain representation structure
     */




    public class ActionEffect
    {

        public int[] conditions;
        public int num_conditions;

        public int[] adds;
        public int num_adds;
        public int[] dels;
        public int num_dels;

        public ActionEffect()
        {

        }
    }




    public class Action : InstTable
    {
        public override string ToString()
        {
            return name;
        }

        public NormOperator norm_operator;
        public PseudoAction pseudo_action;
        public bool axiom;
        public int stratum;

        public string name;
        public int num_name_vars;
        public int[] name_inst_table { get; private set; }



        public Array<int> preconds;
        public int num_preconds;

        public InitializedArray<ActionEffect> effects;
        public int num_effects;

        public Action next;


        public Action()
        {
            name_inst_table = new int[Constants.MAX_VARS];
        }
        public Action(NormOperator no, EasyTemplate et)
        {
            name_inst_table = new int[Constants.MAX_VARS];
            norm_operator = no;
            axiom = no.action_operator.axiom;
            stratum = no.action_operator.stratum;
            for (int i = 0; i < no.num_vars; i++)
            {
                inst_table[i] = et.inst_table[i];
            }
            name = no.action_operator.name;
            num_name_vars = no.action_operator.number_of_real_params;
            make_name_inst_table_from_NormOperator(no, et);
        }

        public Action(PseudoAction pa)
        {
            name_inst_table = new int[Constants.MAX_VARS];
            pseudo_action = pa;
            axiom = pa.action_operator.axiom;
            stratum = pa.action_operator.stratum;
            for (int j = 0; j < pa.action_operator.num_vars; j++)
            {
                inst_table[j] = pa.inst_table[j];
            }
            name = pa.action_operator.name;
            num_name_vars = pa.action_operator.number_of_real_params;
            make_name_inst_table_from_PseudoAction(pa);
        }

        public void make_name_inst_table_from_NormOperator(NormOperator o, EasyTemplate t)
        {
            int i, r = 0, m = 0;

            for (i = 0; i < o.action_operator.number_of_real_params; i++)
            {
                if (o.num_removed_vars > r &&
                 o.removed_vars[r] == i)
                {
                    /* this var has been removed in NormOp;
                     * insert type constraint constant
                     *
                     * at least one there, as empty typed pars ops are removed
                     */
                    name_inst_table[i] = FF.DP.gtype_consts[o.type_removed_vars[r], 0];
                    r++;
                }
                else
                {
                    /* this par corresponds to par m  in NormOp
                     */
                    name_inst_table[i] = t.inst_table[m];
                    name += " " + FF.DP.gconstants[name_inst_table[i]];

                    m++;
                }
            }

        }

        void make_name_inst_table_from_PseudoAction(PseudoAction pa)

        {

            int i;

            for (i = 0; i < pa.action_operator.number_of_real_params; i++)
            {
                name_inst_table[i] = pa.inst_table[i];
                name += " " + FF.DP.gconstants[name_inst_table[i]];

            }

        }

    }












    /*****************************************************
     * BASIC OP AND FT STRUCTURES FOR CONNECTIVITY GRAPH *
     *****************************************************/











    public class OpConn
    {

        /* to get name
         */
        public Action action;
        public bool axiom;
        public int stratum;

        /* effects
         */
        public int[] E;
        public int num_E;

        /* member for applicable actions extraction
         */
        public bool is_in_axA;
        public bool is_in_naxA;

        /* members for 1Ph - H(S) extraction
         */
        public int is_used;
        public bool is_in_H;

    }


    public class Array<T> 
    {
        public T[] array;

        public int Length { get { return array.Length; } }

        public T this[int i]
        {
            get
            {
                return array[i];
            }
            set
            {
                //if (value is int x && x == -1)
               //    Utilities.Write("**");
                array[i] = value;
            }
        }
        public Array(int iSize)
        {
            array = new T[iSize];
        }
        public Array(T[] a)
        {
            array = a;
        }
        public static implicit operator Array<T>(T[] a)
        {
            return new Array<T>(a);
        }

    }    

    public class EfConn
    {

        public int op;

        /* op preconds + conds
         */
        public Array<int> PC;
        public int num_PC;

        public int[] A;
        public int num_A;

        public int[] D;
        public int num_D;

        /* implied effects
         */
        public int[] I;
        public int num_I;

        public bool removed;

        /* members for relaxed fixpoint computation
         */
        public int level;
        public bool in_E;
        public int num_active_PCs;
        public bool ch;

        /* in search: which ef is ``in plan''
         */
        public bool in_plan;

        public EfConn()
        {

        }
    }




    public class FtConn
    {

        /* effects it is union conds, pres element of
         */
        public int[] PC;
        public int num_PC;

        /* efs that add or del it
         */
        public int[] A;
        public int num_A;

        public int[] D;
        public int num_D;

        /* members for orderings preprocessing
         */
        public int[] False;
        public int num_False;

        /* members for relaxed fixpopublic int computation
         */
        public int level;
        public bool in_F;

        /* for faster get_A implementation: either
         * only the axioms or only the non-axioms
         *
         * ax effects it is union conds, pres element of
         */
        public int[] axPC;
        public int num_axPC;
        public int[] naxPC;
        public int num_naxPC;

        /* members for 1Ph extraction
         */
        public int is_goal;
        public int is_true;
        public bool ch;

        /* search
         */
        public int rand;/* for hashing */
        public bool is_global_goal;/* fast goal add finding */

        public bool axiom_add;
        public bool axiom_del;

    }













    /****************************
     * STRUCTURES FOR SEARCHING *
     ****************************/









    public class FFState
    {

        public int[] F;
        public int num_F;

        public int max_F;

        public FFState(int n)
        {
            num_F = 0;
            F = new int[n];
        }

        public FFState()
        {
        }

    }




    public class EhcNode
    {

        public FFState S;

        public int op;
        public int depth;

        public EhcNode father;
        public EhcNode next;

        /* for Goal Added Deletion Heuristic:
         * number of new goal that came in public into S;
         *
         * if no such goal -. == -1
         */
        public int new_goal;

        public EhcNode()
        {
            new_goal = -1;
            S = new FFState(1);
            S.max_F = 0;
        }
    }




    public class EhcHashEntry
    {

        public int sum;

        public EhcNode ehc_node;

        public EhcHashEntry next;

    }




    public class PlanHashEntry
    {

        public int sum;
        public FFState S;

        /* step is number of op that is EXECUTED in S;
         * -1 means that this state is no longer contained in plan
         */
        public int step;
        public PlanHashEntry next_step;

        public PlanHashEntry next;


        public PlanHashEntry()
        {
            S = new FFState();
        }
    }




    public class BfsNode
    {

        public FFState S;

        public int op;
        public int h;

        public BfsNode father;

        public BfsNode next;
        public BfsNode prev;

        public BfsNode()
        {
            S = new FFState();
        }

    }




    public class BfsHashEntry
    {

        public int sum;

        public BfsNode bfs_node;

        public BfsHashEntry next;

    }


    

    public class InitializedArray<T> where T: new()
    {
        public T[] Array;

        public T this[int i]
        {
            get
            {
                return Array[i];
            }
            set
            {
                //if (value is int x && x == -1)
                //    Utilities.Write("*");
                Array[i] = value;
            }
        }

        public int Length { get {  return Array.Length; } }

        public InitializedArray(int iSize)
        {
            Array = new T[iSize];
            for (int j = 0; j < iSize; j++)
                Array[j] = new T();
        }

        public static implicit operator T[](InitializedArray<T> a)
        {
            return a.Array;
        }
        public static implicit operator InitializedArray<T>(T[] a)
        {
            InitializedArray<T> ia = new InitializedArray<T>(1);
            ia.Array = a;
            for (int j = 0; j < a.Length; j++)
                ia.Array[j] = new T();
            return ia;
        }
    }

    public class Array2D<T>
    {
        public T[][] Array;

        public T this[int i, int j]
        {
            get
            {
                return Array[i][j];
            }
            set
            {
                //if (value is int x && x == -1)
                //    Utilities.Write("*");
                Array[i][j] = value;
            }
        }

        public T[] this[int i]
        {
            get
            {
                return Array[i];
            }
            set
            {
                //if (value is int x && x == -1)
                //    Utilities.Write("*");
                Array[i] = value;
            }
        }

        public Array2D(int iSize)
        {
            Array = new T[iSize][];
        }

        public void Init(int i, int iSize)
        {
            Array[i] = new T[iSize];

        }
    }


}
