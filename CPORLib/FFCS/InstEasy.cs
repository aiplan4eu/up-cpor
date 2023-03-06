using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{

    using static CPORLib.FFCS.FFUtilities;



    public class InstEasy
    {

        public  void build_easy_action_templates()
        {

            int i, j;
            NormOperator o;

            cleanup_easy_domain();

            if (gcmd_line.display_info == 110)
            {
                FFUtilities.Write("\n\ncleaned up easy operators are:\n");
                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    Output.print_NormOperator(FF.DP.geasy_operators[i]);
                }
            }

            encode_easy_unaries_as_types();

            if (gcmd_line.display_info == 111)
            {
                FFUtilities.Write("\n\nunaries encoded easy operators are:\n");
                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    Output.print_NormOperator(FF.DP.geasy_operators[i]);
                }
            }

            multiply_easy_effect_parameters();

            if (gcmd_line.display_info == 112)
            {
                FFUtilities.Write("\n\neffects multiplied easy operators are:\n");
                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    Output.print_NormOperator(FF.DP.geasy_operators[i]);
                }
            }

            multiply_easy_op_parameters();

            if (gcmd_line.display_info == 113)
            {
                FFUtilities.Write("\n\ninertia free easy operators are:");
                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    Output.print_NormOperator(FF.DP.geasy_operators[i]);
                }
                FFUtilities.Write("\n\n");
            }

            if (gcmd_line.display_info == 114)
            {
                FFUtilities.Write("\n\neasy operator templates are:\n");

                for (i = 0; i < FF.DP.gnum_easy_operators; i++)
                {
                    o = FF.DP.geasy_operators[i];

                    FFUtilities.Write("\n\n-----------operator %s:-----------", o.action_operator.name);
                    for (EasyTemplate t = FF.DP.geasy_templates; t != null; t = t.next)
                    {
                        if (t.op != o)
                        {
                            continue;
                        }
                        FFUtilities.Write("\ninst: ");
                        for (j = 0; j < o.num_vars; j++)
                        {
                            if (t.inst_table[j] < 0)
                            {
                                FFUtilities.Write("\nuninstantiated param in template! debug me, please\n\n");
                                Exit(1);
                            }
                            FFUtilities.Write("x%d = %s", j, FF.DP.gconstants[t.inst_table[j]]);
                            if (j < o.num_vars - 1)
                            {
                                FFUtilities.Write(", ");
                            }
                        }
                    }
                }
            }

        }











        /*********************************
         * EASY DOMAIN CLEANUP FUNCTIONs *
         *********************************/











        public  void cleanup_easy_domain()

        {

            int i, i1, i2, i3, i4, a;
            NormOperator o;

            /* unused params can result from unary encoding;
             * that's why we have an extra function here
             */
            remove_unused_easy_parameters();


            /* most likely ( for sure ? ) we do not need this function call here,
             * as empty types are recognised in translation already.
             *
             * however, who knows .. ? doesn't need any real computation time anyway.
             *
             * function DOES make sense after unaries encoding, as artificial types
             * miFF.Search.gHt well be empty.
             */
            handle_empty_easy_parameters();


            /* remove identical preconds and effects;
             * VERY unlikely that such will get down to here, after all
             * the formula preprocessing, but possible (?) in principle.
             * takes no computation time.
             *
             * also, remove effect conditions that are contained in the 
             * preconditions.
             */
            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                o = FF.DP.geasy_operators[i];

                i1 = 0;
                while (i1 < o.num_preconds - 1)
                {
                    i2 = i1 + 1;
                    while (i2 < o.num_preconds)
                    {
                        if (identical_fact(o.preconds[i1], o.preconds[i2]))
                        {
                            for (i3 = i2; i3 < o.num_preconds - 1; i3++)
                            {
                                o.preconds[i3].predicate = o.preconds[i3 + 1].predicate;
                                for (i4 = 0; i4 < FF.DP.garity[o.preconds[i3].predicate]; i4++)
                                {
                                    o.preconds[i3].args[i4] = o.preconds[i3 + 1].args[i4];
                                }
                            }
                            o.num_preconds--;
                        }
                        else
                        {
                            i2++;
                        }
                    }
                    i1++;
                }

                for(NormEffect e = o.effects; e != null; e = e.next)
                {

                    i1 = 0;
                    while (i1 < e.num_conditions - 1)
                    {
                        i2 = i1 + 1;
                        while (i2 < e.num_conditions)
                        {
                            if (identical_fact(e.conditions[i1], e.conditions[i2]))
                            {
                                for (i3 = i2; i3 < e.num_conditions - 1; i3++)
                                {
                                    e.conditions[i3].predicate = e.conditions[i3 + 1].predicate;
                                    /* here, we can still have equalities. nowhere else.
                                     */
                                    a = (e.conditions[i3].predicate < 0) ?
                                  2 : FF.DP.garity[e.conditions[i3].predicate];
                                    for (i4 = 0; i4 < a; i4++)
                                    {
                                        e.conditions[i3].args[i4] = e.conditions[i3 + 1].args[i4];
                                    }
                                }
                                e.num_conditions--;
                            }
                            else
                            {
                                i2++;
                            }
                        }
                        i1++;
                    }

                    i1 = 0;
                    while (i1 < e.num_conditions)
                    {
                        for (i2 = 0; i2 < o.num_preconds; i2++)
                        {
                            if (identical_fact(e.conditions[i1], o.preconds[i2]))
                            {
                                break;
                            }
                        }
                        if (i2 == o.num_preconds)
                        {
                            i1++;
                            continue;
                        }
                        for (i2 = i1; i2 < e.num_conditions - 1; i2++)
                        {
                            e.conditions[i2].predicate = e.conditions[i2 + 1].predicate;
                            for (i3 = 0; i3 < FF.DP.garity[e.conditions[i2].predicate]; i3++)
                            {
                                e.conditions[i2].args[i3] = e.conditions[i2 + 1].args[i3];
                            }
                        }
                        e.num_conditions--;
                    }

                    i1 = 0;
                    while (i1 < e.num_adds - 1)
                    {
                        i2 = i1 + 1;
                        while (i2 < e.num_adds)
                        {
                            if (identical_fact(e.adds[i1], e.adds[i2]))
                            {
                                for (i3 = i2; i3 < e.num_adds - 1; i3++)
                                {
                                    e.adds[i3].predicate = e.adds[i3 + 1].predicate;
                                    for (i4 = 0; i4 < FF.DP.garity[e.adds[i3].predicate]; i4++)
                                    {
                                        e.adds[i3].args[i4] = e.adds[i3 + 1].args[i4];
                                    }
                                }
                                e.num_adds--;
                            }
                            else
                            {
                                i2++;
                            }
                        }
                        i1++;
                    }

                    i1 = 0;
                    while (i1 < e.num_dels - 1)
                    {
                        i2 = i1 + 1;
                        while (i2 < e.num_dels)
                        {
                            if (identical_fact(e.dels[i1], e.dels[i2]))
                            {
                                for (i3 = i2; i3 < e.num_dels - 1; i3++)
                                {
                                    e.dels[i3].predicate = e.dels[i3 + 1].predicate;
                                    for (i4 = 0; i4 < FF.DP.garity[e.dels[i3].predicate]; i4++)
                                    {
                                        e.dels[i3].args[i4] = e.dels[i3 + 1].args[i4];
                                    }
                                }
                                e.num_dels--;
                            }
                            else
                            {
                                i2++;
                            }
                        }
                        i1++;
                    }
                }
            }

        }



         bool identical_fact(Fact f1, Fact f2)

        {

            int i, a;

            if (f1.predicate != f2.predicate)
            {
                return false;
            }

            a = (f1.predicate < 0) ? 2 : FF.DP.garity[f1.predicate];

            for (i = 0; i < a; i++)
            {
                if (f1.args[i] != f2.args[i])
                {
                    return false;
                }
            }

            return true;

        }



        public  void remove_unused_easy_parameters()

        {

            int i, i1, i2, i3, a;
            
            bool[] used = new bool[Constants.MAX_VARS];
            NormOperator o;

            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                o = FF.DP.geasy_operators[i];
                for (i1 = 0; i1 < Constants.MAX_VARS; i1++)
                {
                    used[i1] = false;
                }

                for (i1 = 0; i1 < o.num_preconds; i1++)
                {
                    for (i2 = 0; i2 < FF.DP.garity[o.preconds[i1].predicate]; i2++)
                    {
                        if (o.preconds[i1].args[i2] < 0)
                        {
                            used[FFUtilities.DECODE_VAR(o.preconds[i1].args[i2])] = true;
                        }
                    }
                }

                for(NormEffect e = o.effects; e != null; e = e.next)
                {
                    for (i1 = 0; i1 < e.num_conditions; i1++)
                    {
                        a = FF.DP.garity[e.conditions[i1].predicate];
                        for (i2 = 0; i2 < a; i2++)
                        {
                            if (e.conditions[i1].args[i2] < 0)
                            {
                                used[FFUtilities.DECODE_VAR(e.conditions[i1].args[i2])] = true;
                            }
                        }
                    }
                    for (i1 = 0; i1 < e.num_adds; i1++)
                    {
                        for (i2 = 0; i2 < FF.DP.garity[e.adds[i1].predicate]; i2++)
                        {
                            if (e.adds[i1].args[i2] < 0)
                            {
                                used[FFUtilities.DECODE_VAR(e.adds[i1].args[i2])] = true;
                            }
                        }
                    }
                    for (i1 = 0; i1 < e.num_dels; i1++)
                    {
                        for (i2 = 0; i2 < FF.DP.garity[e.dels[i1].predicate]; i2++)
                        {
                            if (e.dels[i1].args[i2] < 0)
                            {
                                used[FFUtilities.DECODE_VAR(e.dels[i1].args[i2])] = true;
                            }
                        }
                    }
                    remove_unused_easy_effect_parameters(o, e);
                }

                i1 = 0;
                i3 = 0;
                while (i1 < o.num_vars)
                {
                    if (used[i1])
                    {
                        i1++;
                    }
                    else
                    {
                        o.type_removed_vars[o.num_removed_vars] = o.var_types[i1];
                        for (i2 = i1; i2 < o.num_vars - 1; i2++)
                        {
                            o.var_types[i2] = o.var_types[i2 + 1];
                            used[i2] = used[i2 + 1];
                        }
                        decrement_var_entries(o, i1);
                        o.num_vars--;
                        o.removed_vars[o.num_removed_vars++] = i3;
                    }
                    i3++;
                }
            }

        }



        public  void decrement_var_entries(NormOperator o, int start)

        {

            int st = FFUtilities.ENCODE_VAR(start), i, j, a;
        

            for (i = 0; i < o.num_preconds; i++)
            {
                for (j = 0; j < FF.DP.garity[o.preconds[i].predicate]; j++)
                {
                    if (o.preconds[i].args[j] < st)
                    {
                        o.preconds[i].args[j]++;
                    }
                }
            }

            for (NormEffect e = o.effects; e != null; e = e.next)
            {
                for (i = 0; i < e.num_conditions; i++)
                {
                    a = FF.DP.garity[e.conditions[i].predicate];
                    for (j = 0; j < a; j++)
                    {
                        if (e.conditions[i].args[j] < st)
                        {
                            e.conditions[i].args[j]++;
                        }
                    }
                }
                for (i = 0; i < e.num_adds; i++)
                {
                    for (j = 0; j < FF.DP.garity[e.adds[i].predicate]; j++)
                    {
                        if (e.adds[i].args[j] < st)
                        {
                            e.adds[i].args[j]++;
                        }
                    }
                }
                for (i = 0; i < e.num_dels; i++)
                {
                    for (j = 0; j < FF.DP.garity[e.dels[i].predicate]; j++)
                    {
                        if (e.dels[i].args[j] < st)
                        {
                            e.dels[i].args[j]++;
                        }
                    }
                }
            }

        }



        public  void remove_unused_easy_effect_parameters(NormOperator o, NormEffect e)

        {

            bool[] used = new bool[Constants.MAX_VARS];
            int i1, i2, i, j, v, a;

            for (i1 = 0; i1 < Constants.MAX_VARS; i1++)
            {
                used[i1] = false;
            }
            for (i1 = 0; i1 < e.num_conditions; i1++)
            {
                a = FF.DP.garity[e.conditions[i1].predicate];
                for (i2 = 0; i2 < a; i2++)
                {
                    if (e.conditions[i1].args[i2] < 0)
                    {
                        used[FFUtilities.DECODE_VAR(e.conditions[i1].args[i2])] = true;
                    }
                }
            }
            for (i1 = 0; i1 < e.num_adds; i1++)
            {
                for (i2 = 0; i2 < FF.DP.garity[e.adds[i1].predicate]; i2++)
                {
                    if (e.adds[i1].args[i2] < 0)
                    {
                        used[FFUtilities.DECODE_VAR(e.adds[i1].args[i2])] = true;
                    }
                }
            }
            for (i1 = 0; i1 < e.num_dels; i1++)
            {
                for (i2 = 0; i2 < FF.DP.garity[e.dels[i1].predicate]; i2++)
                {
                    if (e.dels[i1].args[i2] < 0)
                    {
                        used[FFUtilities.DECODE_VAR(e.dels[i1].args[i2])] = true;
                    }
                }
            }

            i1 = 0;
            while (i1 < e.num_vars)
            {
                v = o.num_vars + i1;
                if (used[v])
                {
                    i1++;
                }
                else
                {
                    for (i2 = i1; i2 < e.num_vars - 1; i2++)
                    {
                        e.var_types[i2] = e.var_types[i2 + 1];
                        used[o.num_vars + i2] = used[o.num_vars + i2 + 1];
                    }
                    /* now decrement var entrys hiFF.Search.gHer than o.num_vars+i1
                     */
                    for (i = 0; i < e.num_conditions; i++)
                    {
                        a = FF.DP.garity[e.conditions[i].predicate];
                        for (j = 0; j < a; j++)
                        {
                            if (e.conditions[i].args[j] < FFUtilities.ENCODE_VAR(v))
                            {
                                e.conditions[i].args[j]++;
                            }
                        }
                    }
                    for (i = 0; i < e.num_adds; i++)
                    {
                        for (j = 0; j < FF.DP.garity[e.adds[i].predicate]; j++)
                        {
                            if (e.adds[i].args[j] < FFUtilities.ENCODE_VAR(v))
                            {
                                e.adds[i].args[j]++;
                            }
                        }
                    }
                    for (i = 0; i < e.num_dels; i++)
                    {
                        for (j = 0; j < FF.DP.garity[e.dels[i].predicate]; j++)
                        {
                            if (e.dels[i].args[j] < FFUtilities.ENCODE_VAR(v))
                            {
                                e.dels[i].args[j]++;
                            }
                        }
                    }
                    e.num_vars--;
                }
            }

        }



        /* this one needs ONLY be used after unaries encoding, as all empty types
         * are already recognised during translation, except the artificial ones,
         * of course.
         */
        public  void handle_empty_easy_parameters()

        {

            int i, j, k;
            NormOperator o;
            NormEffect e, tmp;

            i = 0;
            while (i < FF.DP.gnum_easy_operators)
            {
                o = FF.DP.geasy_operators[i];

                for (j = 0; j < o.num_vars; j++)
                {
                    if (FF.DP.gtype_size[o.var_types[j]] == 0)
                    {
                        break;
                    }
                }
                if (j < o.num_vars)
                {
                    //free_NormOperator(o);
                    for (k = i; k < FF.DP.gnum_easy_operators - 1; k++)
                    {
                        FF.DP.geasy_operators[k] = FF.DP.geasy_operators[k + 1];
                    }
                    FF.DP.gnum_easy_operators--;
                }
                else
                {
                    i++;
                }
            }

            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                o = FF.DP.geasy_operators[i];

                e = o.effects;
                while (e != null)
                {
                    for (j = 0; j < e.num_vars; j++)
                    {
                        if (FF.DP.gtype_size[e.var_types[j]] == 0)
                        {
                            break;
                        }
                    }
                    if (j < e.num_vars)
                    {
                        if (e.prev != null)
                        {
                            e.prev.next = e.next;
                        }
                        else
                        {
                            o.effects = e.next;
                        }
                        if (e.next != null)
                        {
                            e.next.prev = e.prev;
                        }
                        tmp = e.next;
                        //free_single_NormEffect(e);
                        e = tmp;
                    }
                    else
                    {
                        e = e.next;
                    }
                }
            }

        }










        /****************************
         * UNARY INERTIA intO TYPES *
         ****************************/












         void encode_easy_unaries_as_types()
        {

            NormOperator o;
            int i1, i, j, k, l, new_T, p, a;
            TypeArray T = new TypeArray();
            int num_T;
            
            int intersected_type, var;

            for (i1 = 0; i1 < FF.DP.gnum_easy_operators; i1++)
            {
                o = FF.DP.geasy_operators[i1];

                for (i = 0; i < o.num_vars; i++)
                {

                    T[0] = o.var_types[i];
                    num_T = 1;

                    j = 0;
                    while (j < o.num_preconds)
                    {
                        p = o.preconds[j].predicate;
                        if (((new_T = FF.Inertia.gtype_to_predicate[p]) != -1) &&
                             (o.preconds[j].args[0] == FFUtilities.ENCODE_VAR(i)))
                        {
                            if (num_T == Constants.MAX_TYPE_INTERSECTIONS)
                            {
                                FFUtilities.Write("\nincrease Constants.MAX_TYPE_INTERSECTIONS (currently %d)\n\n",
                                   Constants.MAX_TYPE_INTERSECTIONS);
                                Exit(1);
                            }
                            /* insert new type number into ordered array T;
                             * ---- all type numbers in T are different:
                             *      new nr. is of inferred type - can't be type declared for param
                             *      precondition facts occur at most once - doubles are removed
                             *                                              during cleanup
                             */
                            for (k = 0; k < num_T; k++)
                            {
                                if (new_T < T[k])
                                {
                                    break;
                                }
                            }
                            for (l = num_T; l > k; l--)
                            {
                                T[l] = T[l - 1];
                            }
                            T[k] = new_T;
                            num_T++;
                            /* now remove superfluous precondition
                             */
                            for (k = j; k < o.num_preconds - 1; k++)
                            {
                                o.preconds[k].predicate = o.preconds[k + 1].predicate;
                                for (l = 0; l < FF.DP.garity[o.preconds[k].predicate]; l++)
                                {
                                    o.preconds[k].args[l] = o.preconds[k + 1].args[l];
                                }
                            }
                            o.num_preconds--;
                        }
                        else
                        {
                            j++;
                        }
                    }

                    /* if we did not hit any unary inertia concerning this parameter
                     * in the preconds, skip parameter and go to next one
                     */
                    if (num_T == 1)
                    {
                        continue;
                    }

                    /* now we have the ordered array of types to intersect for param i 
                     * of op o in array T of size num_T;
                     * if there already is this intersected type, set type of this
                     * param to its number, otherwise create the new intersected type.
                     */
                    if ((intersected_type = find_intersected_type(T, num_T)) != -1)
                    {
                        /* type already there
                         */
                        o.var_types[i] = intersected_type;
                        continue;
                    }

                    /* create new type
                     */
                    o.var_types[i] = create_intersected_type(T, num_T);
                }

                for(NormEffect e = o.effects; e != null; e = e.next)
                {
                    for (i = 0; i < e.num_vars; i++)
                    {
                        T[0] = e.var_types[i];
                        var = o.num_vars + i;
                        num_T = 1;
                        j = 0;
                        while (j < e.num_conditions)
                        {
                            p = e.conditions[j].predicate;
                            if (p < 0)
                            {
                                j++;
                                continue;
                            }
                            if (((new_T = FF.Inertia.gtype_to_predicate[p]) != -1) &&
                                 (e.conditions[j].args[0] == FFUtilities.ENCODE_VAR(var)))
                            {
                                if (num_T == Constants.MAX_TYPE_INTERSECTIONS)
                                {
                                    FFUtilities.Write("\nincrease Constants.MAX_TYPE_INTERSECTIONS (currently %d)\n\n",
                                       Constants.MAX_TYPE_INTERSECTIONS);
                                    Exit(1);
                                }
                                for (k = 0; k < num_T; k++)
                                {
                                    if (new_T < T[k])
                                    {
                                        break;
                                    }
                                }
                                for (l = num_T; l > k; l--)
                                {
                                    T[l] = T[l - 1];
                                }
                                T[k] = new_T;
                                num_T++;
                                for (k = j; k < e.num_conditions - 1; k++)
                                {
                                    e.conditions[k].predicate = e.conditions[k + 1].predicate;
                                    a = (e.conditions[k].predicate < 0) ?
                                  2 : FF.DP.garity[e.conditions[k].predicate];
                                    for (l = 0; l < a; l++)
                                    {
                                        e.conditions[k].args[l] = e.conditions[k + 1].args[l];
                                    }
                                }
                                e.num_conditions--;
                            }
                            else
                            {
                                j++;
                            }
                        }
                        if (num_T == 1)
                        {
                            continue;
                        }
                        if ((intersected_type = find_intersected_type(T, num_T)) != -1)
                        {
                            e.var_types[i] = intersected_type;
                            continue;
                        }
                        e.var_types[i] = create_intersected_type(T, num_T);
                    }
                }
            }

            remove_unused_easy_parameters();
            handle_empty_easy_parameters();

        }



        public  int create_intersected_type(TypeArray T, int num_T)

        {

            int i, j, k, intersected_type;

            if (FF.DP.gnum_types == Constants.MAX_TYPES)
            {
                FFUtilities.Write("\ntoo many (inferred and intersected) types! increase Constants.MAX_TYPES (currently %d)\n\n",
                   Constants.MAX_TYPES);
                Exit(1);
            }
            FF.DP.gtype_names[FF.DP.gnum_types] = null;
            FF.DP.gtype_size[FF.DP.gnum_types] = 0;
            for (i = 0; i <Constants.MAX_CONSTANTS; i++)
            {
                FF.DP.gis_member[i,FF.DP.gnum_types] = false;
            }
            for(j = 0; j < FF.DP.gnum_types + 1; j++)
            {
                if (FF.Inertia.gintersected_types[j] == null)
                    FF.Inertia.gintersected_types[j] = new TypeArray();
            }

            for (i = 0; i < num_T; i++)
            {
                FF.Inertia.gintersected_types[FF.DP.gnum_types][i] = T[i];
            }
            FF.Inertia.gnum_intersected_types[FF.DP.gnum_types] = num_T;
            intersected_type = FF.DP.gnum_types;
            FF.DP.gnum_types++;

            for (j = 0; j < FF.DP.gtype_size[T[0]]; j++)
            {
                for (k = 1; k < num_T; k++)
                {
                    if (!FF.DP.gis_member[FF.DP.gtype_consts[T[0], j], T[k]])
                    {
                        break;
                    }
                }
                if (k < num_T)
                {
                    continue;
                }
                /* add constant to new type
                 */
                if (FF.DP.gtype_size[intersected_type] == Constants.MAX_TYPE)
                {
                    FFUtilities.Write("\ntoo many consts in intersected type! increase Constants.MAX_TYPE (currently %d)\n\n",
                       Constants.MAX_TYPE);
                    Exit(1);
                }
                FF.DP.gtype_consts[intersected_type,FF.DP.gtype_size[intersected_type]++] = FF.DP.gtype_consts[T[0],j];
                FF.DP.gis_member[FF.DP.gtype_consts[T[0],j],intersected_type] = true;
            }

            /* now verify if the intersected type equals one of the types that we intersected.
             * this is the case, iff one of the types in T has the same size as intersected_type
             */
            for (j = 0; j < num_T; j++)
            {
                if (FF.DP.gtype_size[intersected_type] != FF.DP.gtype_size[T[j]])
                {
                    continue;
                }
                /* type T[j] contains exactly the constants that we need!
                 *
                 * remove intersected type from table!
                 */
                FF.DP.gtype_size[intersected_type] = 0;
                for (k = 0; k <Constants.MAX_CONSTANTS; k++)
                {
                    FF.DP.gis_member[k,intersected_type] = false;
                }
                FF.Inertia.gnum_intersected_types[intersected_type] = -1;
                FF.DP.gnum_types--;
                intersected_type = T[j];
                break;
            }

            return intersected_type;

        }



        public  int find_intersected_type(TypeArray T, int num_T)

        {

            int i, j;

            for (i = 0; i < FF.DP.gnum_types; i++)
            {
                if (FF.Inertia.gnum_intersected_types[i] == -1)
                {
                    continue;
                }

                if (FF.Inertia.gnum_intersected_types[i] != num_T)
                {
                    continue;
                }

                for (j = 0; j < num_T; j++)
                {
                    if (T[j] != FF.Inertia.gintersected_types[i][j])
                    {
                        break;
                    }
                }
                if (j < num_T)
                {
                    continue;
                }

                return i;
            }

            return -1;

        }














        /******************************
         * MULTIPLY EFFECT PARAMETERS *
         ******************************/












        /* local globals for multiplying
         */

         int[] linertia_conds = new int[Constants.MAX_VARS];
         int lnum_inertia_conds;

         int[] lmultiply_parameters = new int[Constants.MAX_VARS];
         int lnum_multiply_parameters;

         NormOperator lo;
         NormEffect le;

         NormEffect lres;






         void multiply_easy_effect_parameters()

        {

            int i, j, k, l, p, par;
            

            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                lo = FF.DP.geasy_operators[i];

                lres = null;
                for (NormEffect e = lo.effects; e != null; e = e.next)
                {
                    le = e;

                    lnum_inertia_conds = 0;
                    for (j = 0; j < e.num_conditions; j++)
                    {
                        for (k = 0; k < FF.DP.garity[e.conditions[j].predicate]; k++)
                        {
                            if (e.conditions[j].args[k] < 0 &&
                                 FFUtilities.DECODE_VAR(e.conditions[j].args[k]) < lo.num_vars)
                            {
                                break;
                            }
                        }
                        if (k < FF.DP.garity[e.conditions[j].predicate])
                        {
                            /* only consider inertia constraining effect parameters
                             */
                            continue;
                        }
                        if (!FF.Inertia.gis_added[e.conditions[j].predicate] &&
                             !FF.Inertia.gis_deleted[e.conditions[j].predicate])
                        {
                            linertia_conds[lnum_inertia_conds++] = j;
                        }
                    }

                    lnum_multiply_parameters = 0;
                    for (j = 0; j < e.num_vars; j++)
                    {
                        par = lo.num_vars + j;
                        for (k = 0; k < lnum_inertia_conds; k++)
                        {
                            p = e.conditions[linertia_conds[k]].predicate;
                            for (l = 0; l < FF.DP.garity[p]; l++)
                            {
                                if (e.conditions[linertia_conds[k]].args[l] ==
                                 FFUtilities.ENCODE_VAR(par))
                                {
                                    break;
                                }
                            }
                            if (l < FF.DP.garity[p])
                            {
                                break;
                            }
                        }
                        if (k < lnum_inertia_conds)
                        {
                            continue;
                        }
                        lmultiply_parameters[lnum_multiply_parameters++] = j;
                    }

                    unify_easy_inertia_conditions(0);
                }
                //free_NormEffect(lo.effects);
                lo.effects = lres;
            }

        }



         void unify_easy_inertia_conditions(int curr_inertia)

        {

            int p, i, j, af, hh;
            int[] args = new int[Constants.MAX_VARS];
            int[] affected_params = new int[Constants.MAX_VARS]; 
            int num_affected_params = 0;

            if (curr_inertia == lnum_inertia_conds)
            {
                multiply_easy_non_constrained_effect_parameters(0);
                return;
            }

            p = le.conditions[linertia_conds[curr_inertia]].predicate;
            for (i = 0; i < FF.DP.garity[p]; i++)
            {
                args[i] = le.conditions[linertia_conds[curr_inertia]].args[i];
                if (args[i] < 0)
                {
                    hh = FFUtilities.DECODE_VAR(args[i]);
                    hh -= lo.num_vars;
                    if (le.inst_table[hh] != -1)
                    {
                        args[i] = le.inst_table[hh];
                    }
                    else
                    {
                        affected_params[num_affected_params++] = hh;
                    }
                }
            }

            for (i = 0; i < FF.DP.gnum_initial_predicate[p]; i++)
            {
                af = 0;
                for (j = 0; j < FF.DP.garity[p]; j++)
                {
                    if (args[j] >= 0)
                    {
                        if (args[j] != FF.DP.ginitial_predicate[p,i].args[j])
                        {
                            break;
                        }
                        else
                        {
                            continue;
                        }
                    }
                    le.inst_table[affected_params[af++]] = FF.DP.ginitial_predicate[p,i].args[j];
                }
                if (j < FF.DP.garity[p])
                {
                    continue;
                }

                unify_easy_inertia_conditions(curr_inertia + 1);
            }

            for (i = 0; i < num_affected_params; i++)
            {
                le.inst_table[affected_params[i]] = -1;
            }

        }



         void multiply_easy_non_constrained_effect_parameters(int curr_parameter)

        {

            int t, n, i, j, k, p, par;
            NormEffect tmp;
            bool rem;

            if (curr_parameter == lnum_multiply_parameters)
            {
                /* create new effect, adjusting conds to inst, and
                 * partially instantiating effects;
                 *
                 * add result to  lres
                 */
                tmp = new NormEffect(le);
                /* instantiate param occurences
                 */
                for (i = 0; i < le.num_vars; i++)
                {
                    par = lo.num_vars + i;
                    for (j = 0; j < tmp.num_conditions; j++)
                    {
                        for (k = 0; k < FF.DP.garity[tmp.conditions[j].predicate]; k++)
                        {
                            if (tmp.conditions[j].args[k] == FFUtilities.ENCODE_VAR(par))
                            {
                                tmp.conditions[j].args[k] = le.inst_table[i];
                            }
                        }
                    }
                    for (j = 0; j < tmp.num_adds; j++)
                    {
                        for (k = 0; k < FF.DP.garity[tmp.adds[j].predicate]; k++)
                        {
                            if (tmp.adds[j].args[k] == FFUtilities.ENCODE_VAR(par))
                            {
                                tmp.adds[j].args[k] = le.inst_table[i];
                            }
                        }
                    }
                    for (j = 0; j < tmp.num_dels; j++)
                    {
                        for (k = 0; k < FF.DP.garity[tmp.dels[j].predicate]; k++)
                        {
                            if (tmp.dels[j].args[k] == FFUtilities.ENCODE_VAR(par))
                            {
                                tmp.dels[j].args[k] = le.inst_table[i];
                            }
                        }
                    }
                }
                /* adjust conditions
                 */
                i = 0;
                while (i < tmp.num_conditions)
                {
                    rem = false;
                    p = tmp.conditions[i].predicate;
                    if (!FF.Inertia.gis_added[p] &&
                     !FF.Inertia.gis_deleted[p])
                    {
                        for (j = 0; j < FF.DP.garity[p]; j++)
                        {
                            if (tmp.conditions[i].args[j] < 0 && tmp.conditions[i].args[j] < lo.num_vars)
                                 //Utilities.DECODE_VAR(tmp.conditions[i].args[j] < lo.num_vars) != 0) //this statement makes no sense to me
                            {
                                break;
                            }
                        }
                        if (j == FF.DP.garity[p])
                        {
                            /* inertia that constrain only effect params have been unified,
                             * are therefore true
                             */
                            rem = true;
                        }
                    }
                    if (rem)
                    {
                        for (j = i; j < tmp.num_conditions - 1; j++)
                        {
                            tmp.conditions[j].predicate = tmp.conditions[j + 1].predicate;
                            for (k = 0; k < FF.DP.garity[tmp.conditions[j + 1].predicate]; k++)
                            {
                                tmp.conditions[j].args[k] = tmp.conditions[j + 1].args[k];
                            }
                        }
                        tmp.num_conditions--;
                    }
                    else
                    {
                        i++;
                    }
                }
                /* add result to lres
                 */
                if (lres != null)
                {
                    lres.prev = tmp;
                }
                tmp.next = lres;
                lres = tmp;
                return;
            }

            t = le.var_types[lmultiply_parameters[curr_parameter]];
            n = FF.DP.gtype_size[t];

            for (i = 0; i < n; i++)
            {
                le.inst_table[lmultiply_parameters[curr_parameter]] = FF.DP.gtype_consts[t,i];
                multiply_easy_non_constrained_effect_parameters(curr_parameter + 1);
            }

            le.inst_table[lmultiply_parameters[curr_parameter]] = -1;

        }



















        /**************************
         * MULTIPLY OP PARAMETERS *
         **************************/


















         void multiply_easy_op_parameters()

        {

            int i, j, k, l, p;
            NormOperator o;

            FF.DP.geasy_templates = null;
            FF.DP.gnum_easy_templates = 0;

            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                lo = FF.DP.geasy_operators[i];

                lnum_inertia_conds = 0;
                for (j = 0; j < lo.num_preconds; j++)
                {
                    if (!FF.Inertia.gis_added[lo.preconds[j].predicate] &&
                     !FF.Inertia.gis_deleted[lo.preconds[j].predicate])
                    {
                        linertia_conds[lnum_inertia_conds++] = j;
                    }
                }

                lnum_multiply_parameters = 0;
                for (j = 0; j < lo.num_vars; j++)
                {
                    for (k = 0; k < lnum_inertia_conds; k++)
                    {
                        p = lo.preconds[linertia_conds[k]].predicate;
                        for (l = 0; l < FF.DP.garity[p]; l++)
                        {
                            if (lo.preconds[linertia_conds[k]].args[l] ==
                                 FFUtilities.ENCODE_VAR(j))
                            {
                                break;
                            }
                        }
                        if (l < FF.DP.garity[p])
                        {
                            break;
                        }
                    }
                    if (k < lnum_inertia_conds)
                    {
                        continue;
                    }
                    lmultiply_parameters[lnum_multiply_parameters++] = j;
                }

                unify_easy_inertia_preconds(0);
            }

            /* now remove inertia preconditions from operator schemata
             */
            for (i = 0; i < FF.DP.gnum_easy_operators; i++)
            {
                o = FF.DP.geasy_operators[i];

                j = 0;
                while (j < o.num_preconds)
                {
                    if (!FF.Inertia.gis_added[o.preconds[j].predicate] &&
                     !FF.Inertia.gis_deleted[o.preconds[j].predicate])
                    {
                        for (k = j; k < o.num_preconds - 1; k++)
                        {
                            o.preconds[k].predicate = o.preconds[k + 1].predicate;
                            for (l = 0; l < FF.DP.garity[o.preconds[k].predicate]; l++)
                            {
                                o.preconds[k].args[l] = o.preconds[k + 1].args[l];
                            }
                        }
                        o.num_preconds--;
                    }
                    else
                    {
                        j++;
                    }
                }
            }

        }



         void unify_easy_inertia_preconds(int curr_inertia)

        {

            int p, i, j, af, hh;
            int[] args = new int[Constants.MAX_VARS];
            int[] affected_params = new int[Constants.MAX_VARS];
            int num_affected_params = 0;

            if (curr_inertia == lnum_inertia_conds)
            {
                multiply_easy_non_constrained_op_parameters(0);
                return;
            }

            p = lo.preconds[linertia_conds[curr_inertia]].predicate;
            for (i = 0; i < FF.DP.garity[p]; i++)
            {
                args[i] = lo.preconds[linertia_conds[curr_inertia]].args[i];
                if (args[i] < 0)
                {
                    hh = FFUtilities.DECODE_VAR(args[i]);
                    if (lo.inst_table[hh] != -1)
                    {
                        args[i] = lo.inst_table[hh];
                    }
                    else
                    {
                        affected_params[num_affected_params++] = hh;
                    }
                }
            }

            for (i = 0; i < FF.DP.gnum_initial_predicate[p]; i++)
            {
                af = 0;
                for (j = 0; j < FF.DP.garity[p]; j++)
                {
                    if (args[j] >= 0)
                    {
                        if (args[j] != FF.DP.ginitial_predicate[p,i].args[j])
                        {
                            break;
                        }
                        else
                        {
                            continue;
                        }
                    }
                    /* check whether that constant has the correct type for that
                     * parameter
                     */
                    if (!FF.DP.gis_member[FF.DP.ginitial_predicate[p,i].args[j],lo.var_types[affected_params[af]]])
                    {
                        break;
                    }
                    /* legal constant; set op parameter instantiation to it
                     */

                    lo.inst_table[affected_params[af++]] = FF.DP.ginitial_predicate[p,i].args[j];
                }
                if (j < FF.DP.garity[p])
                {
                    continue;
                }

                unify_easy_inertia_preconds(curr_inertia + 1);
            }

            for (i = 0; i < num_affected_params; i++)
            {
                lo.inst_table[affected_params[i]] = -1;
            }

        }



         void multiply_easy_non_constrained_op_parameters(int curr_parameter)

        {

            EasyTemplate tmp;
            int i, j, t, n;

            if (curr_parameter == lnum_multiply_parameters)
            {
                tmp = new EasyTemplate(lo);
                for (i = 0; i < lo.num_vars; i++)
                {
                    tmp.inst_table[i] = lo.inst_table[i];
                }
                tmp.next = FF.DP.geasy_templates;
                if (FF.DP.geasy_templates != null)
                {
                    FF.DP.geasy_templates.prev = tmp;
                }
                FF.DP.geasy_templates = tmp;
                FF.DP.gnum_easy_templates++;
                return;
            }

            if (curr_parameter == lnum_multiply_parameters - 1)
            {
                t = lo.var_types[lmultiply_parameters[curr_parameter]];
                n = FF.DP.gtype_size[t];
                for (i = 0; i < n; i++)
                {
                    lo.inst_table[lmultiply_parameters[curr_parameter]] = FF.DP.gtype_consts[t,i];

                    tmp = new EasyTemplate(lo);
                    for (j = 0; j < lo.num_vars; j++)
                    {
                        tmp.inst_table[j] = lo.inst_table[j];
                    }
                    tmp.next = FF.DP.geasy_templates;
                    if (FF.DP.geasy_templates != null)
                    {
                        FF.DP.geasy_templates.prev = tmp;
                    }
                    FF.DP.geasy_templates = tmp;
                    FF.DP.gnum_easy_templates++;
                }

                lo.inst_table[lmultiply_parameters[curr_parameter]] = -1;

                return;
            }

            t = lo.var_types[lmultiply_parameters[curr_parameter]];
            n = FF.DP.gtype_size[t];
            for (i = 0; i < n; i++)
            {
                lo.inst_table[lmultiply_parameters[curr_parameter]] = FF.DP.gtype_consts[t,i];

                multiply_easy_non_constrained_op_parameters(curr_parameter + 1);
            }

            lo.inst_table[lmultiply_parameters[curr_parameter]] = -1;

        }

    }
}
