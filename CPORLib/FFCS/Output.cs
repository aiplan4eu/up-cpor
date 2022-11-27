using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading.Tasks;

using static CPORLib.FFCS.Connective;

namespace CPORLib.FFCS
{
    public class Output
    {

        internal static void print_Action(Action a)
        {
            FFUtilities.WriteLine(a.name);
        }

        internal static void print_Fact2(Fact fact)
        {
            FFUtilities.Write("Fact: " + fact.predicate + " args: ");

            for (int i = 0; i < fact.args.Length; i++)
                FFUtilities.Write(fact.args[i] + ",");
            FFUtilities.WriteLine();
        }


       
        internal static void print_Fact(Fact f)
    {

        int j;

        if (f.predicate == -3)
        {
            FFUtilities.Write("GOAL-REACHED");
            return;
        }

        if (f.predicate == -1)
        {
            FFUtilities.Write("=(");
            for (j = 0; j < 2; j++)
            {
                if (f.args[j] >= 0)
                {
                    FFUtilities.Write(FF.DP.gconstants[(f.args)[j]]);
                }
                else
                {
                    FFUtilities.Write("x" + FFUtilities.DECODE_VAR(f.args[j]));
                }
                if (j < 1)
                {
                    FFUtilities.Write(" ");
                }
            }
            FFUtilities.Write(")");
            return;
        }

        if (f.predicate == -2)
        {
            FFUtilities.Write("!=(");
            for (j = 0; j < 2; j++)
            {
                if (f.args[j] >= 0)
                {
                    FFUtilities.Write(FF.DP.gconstants[(f.args)[j]]);
                }
                else
                {
                    FFUtilities.Write("x" + FFUtilities.DECODE_VAR(f.args[j]));
                }
                if (j < 1)
                {
                    FFUtilities.Write(" ");
                }
            }
            FFUtilities.Write(")");
            return;
        }

        FFUtilities.Write(FF.DP.gpredicates[f.predicate] + "(");
        for (j = 0; j < FF.DP.garity[f.predicate]; j++)
        {
            if (f.args[j] >= 0)
            {
                FFUtilities.Write(FF.DP.gconstants[(f.args)[j]]);
            }
            else
            {
                FFUtilities.Write("x" + FFUtilities.DECODE_VAR(f.args[j]));
            }
            if (j < FF.DP.garity[f.predicate] - 1)
            {
                FFUtilities.Write(" ");
            }
        }
        FFUtilities.Write(")");

    }




        internal static void print_ft_name(int index)
        {
            print_Fact(FF.DP.grelevant_facts[index]);
        }

        internal static void print_MixedOperator(MixedOperator o)
        {
            throw new NotImplementedException();
        }

        internal static void print_NormOperator(NormOperator normOperator)
        {
            throw new NotImplementedException();
        }

        internal static void print_Operator(Operator @operator)
        {
            throw new NotImplementedException();
        }

        internal static void print_op_name(int index)
        {
            int i;
            Action a = FF.CF.gop_conn[index].action;

            if (a.norm_operator == null &&
                 a.pseudo_action == null)
            {
                FFUtilities.WriteLine("REACH-GOAL");
            }
            else
            {
                FFUtilities.Write(a.name);
                /*
                for (i = 0; i < a.num_name_vars; i++)
                {
                    Utilities.Write(" " + Main.DP.gconstants[a.name_inst_table[i]]);
                }
                */
            }
        }


        internal static string GetFullName(int index)
        {
            int i;
            Action a = FF.CF.gop_conn[index].action;

            if (a.norm_operator == null &&
                 a.pseudo_action == null)
            {
                return "REACH-GOAL";
            }
            else
            {
                string s = a.name;
                
                for (i = 0; i < a.num_name_vars; i++)
                {
                    s += " " + FF.DP.gconstants[a.name_inst_table[i]];
                }
                return s;
            }
        }


        internal static void print_PlNode(PlNode plnode, int indent)
        {
         

            PlNode i_son;

            if (plnode == null)
            {
                FFUtilities.Write("none\n");
                return;
            }

            switch (plnode.connective)
            {
                case ALL:
                    FFUtilities.WriteLine("ALL\n" + plnode.atom.item + ":" +
                        plnode.atom.next.item);
                    print_indent(indent);
                    FFUtilities.Write("(   ");
                    print_PlNode(plnode.sons, indent + 4);
                    print_indent(indent);
                    FFUtilities.Write(")\n");
                    break;
                case EX:
                    FFUtilities.Write("EX\n" + plnode.atom.item + ":" +
                        plnode.atom.next.item);
                    print_indent(indent);
                    FFUtilities.Write("(   ");
                    print_PlNode(plnode.sons, indent + 4);
                    print_indent(indent);
                    FFUtilities.Write(")\n");
                    break;
                case AND:
                    FFUtilities.Write("AND(  ");
                    print_PlNode(plnode.sons, indent + 4);
                    if (plnode.sons != null)
                    {
                        for (i_son = plnode.sons.next; i_son != null; i_son = i_son.next)
                        {
                            print_indent(indent);
                            FFUtilities.Write("AND ");
                            print_PlNode(i_son, indent + 4);
                        }
                    }
                    print_indent(indent);
                    FFUtilities.Write(")\n");
                    break;
                case OR:
                    FFUtilities.Write("OR(  ");
                    print_PlNode(plnode.sons, indent + 4);
                    for (i_son = plnode.sons.next; i_son != null; i_son = i_son.next)
                    {
                        print_indent(indent);
                        FFUtilities.Write("OR ");
                        print_PlNode(i_son, indent + 4);
                    }
                    print_indent(indent);
                    FFUtilities.Write(")\n");
                    break;
                case WHEN:
                    FFUtilities.Write("IF   ");
                    print_PlNode(plnode.sons, indent + 5);
                    print_indent(indent);
                    FFUtilities.Write("THEN ");
                    print_PlNode(plnode.sons.next, indent + 5);
                    print_indent(indent);
                    FFUtilities.Write("ENDIF\n");
                    break;
                case NOT:
                    if (ATOM == plnode.sons.connective)
                    {
                        FFUtilities.Write("NOT ");
                        print_PlNode(plnode.sons, indent + 4);
                    }
                    else
                    {
                        FFUtilities.Write("NOT(");
                        print_PlNode(plnode.sons, indent + 4);
                        print_indent(indent + 3);
                        FFUtilities.Write(")\n");
                    }
                    break;
                case ATOM:
                    FFUtilities.Write("(");
                    print_hidden_TokenList(plnode.atom, " ");
                    FFUtilities.Write(")\n");
                    break;
                case TRU:
                    FFUtilities.Write("(TRUE)\n");
                    break;
                case FAL:
                    FFUtilities.Write("(FALSE)\n");
                    break;
                default:
                    FFUtilities.Write("\n***** ERROR ****");
                    FFUtilities.Write("\nprint_plnode: %d > Wrong Node specifier\n", plnode.connective);
                    FFUtilities.Exit(1);
                    break;
            }

        }

        private static void print_hidden_TokenList(TokenList atom, string s)
        {
            FFUtilities.Write(atom.ToString());
        }

        private static void print_indent(int indent)
        {
            for (int i = 0; i < indent; i++)
                FFUtilities.Write(" ");
        }

        internal static void print_plops(PlOperator plop)
        {
            PlOperator i_plop;
            int count = 0;

            if (plop == null)
            {
                FFUtilities.Write("none\n");
                return;
            }

            for (i_plop = plop; i_plop != null; i_plop = i_plop.next)
            {
                FFUtilities.Write("\n");
                if (i_plop.axiom) FFUtilities.Write("AXIOM-");
                FFUtilities.Write("OPERATOR ");
                FFUtilities.Write(i_plop.name);
                FFUtilities.Write("\nparameters: " + i_plop.number_of_real_params + "\n");

                print_FactList(i_plop.parameters, "\n", " : ");
                FFUtilities.Write("\n\npreconditions:\n");
                print_PlNode(i_plop.preconds, 0);
                FFUtilities.Write("effects:\n");
                print_PlNode(i_plop.effects, 0);
                FFUtilities.Write("\n-----\n");
                count++;
            }
            FFUtilities.WriteLine("\nnumber of operators: " + count);
        }

        private static void print_FactList(FactList list, string sepf, string sept)
        {

            FactList i_list;
            TokenList i_tl;

            if (list != null)
            {
                i_tl = list.item;
                if (null == i_tl || null == i_tl.item)
                {
                    FFUtilities.Write("empty");
                }
                else
                {
                    FFUtilities.Write(i_tl.item);
                    i_tl = i_tl.next;
                }

                while (null != i_tl)
                {
                    if (null != i_tl.item)
                    {
                        FFUtilities.Write( sept + i_tl.item);
                    }
                    i_tl = i_tl.next;
                }

                for (i_list = list.next; i_list != null; i_list = i_list.next)
                {
                    FFUtilities.Write(sepf);
                    i_tl = i_list.item;
                    if (null == i_tl || null == i_tl.item)
                    {
                        FFUtilities.Write("empty");
                    }
                    else
                    {
                        FFUtilities.Write(i_tl.item);
                        i_tl = i_tl.next;
                    }

                    while (null != i_tl)
                    {
                        if (null != i_tl.item)
                        {
                            FFUtilities.Write( sept + i_tl.item);
                        }
                        i_tl = i_tl.next;
                    }
                }
            }

        }

        internal static void print_PseudoAction(PseudoAction pseudoAction)
        {
            throw new NotImplementedException();
        }

        internal static void print_Wff(WffNode ggoal, int v)
        {
            throw new NotImplementedException();
        }
    }
}
