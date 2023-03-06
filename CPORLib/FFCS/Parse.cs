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

using static CPORLib.FFCS.Parsing;


namespace CPORLib.FFCS
{
    public class Parse
    {









        /* simple parse helpers
         */








         TokenList copy_TokenList(TokenList source)

        {

            TokenList temp;

            if( null == source)
            {
                temp = null;
            }
            else
            {
                temp = new TokenList(source.item);
                
                temp.next = copy_TokenList(source.next);
            }

            return temp;

        }






         string rmdash(string s)

        {
            int idx1 = s.IndexOf(' ');
            int idx2 = s.IndexOf('\t');

            int idx = idx1;
            if (idx == -1)
                idx = idx2;
            if (idx == -1)
                return "";
            string sTag = s.Substring(idx + 1);

            return sTag;

        }










        /* typed-list-of   preprocessing
         */







         string[] ltype_names = new string[MAX_TYPES];
         int lnum_types;


         int[,] leither_ty = new int[MAX_TYPES,MAX_TYPES];
         int[] lnum_either_ty = new int[MAX_TYPES];



        int get_type(string str)
        {

            int i;

            for (i = 0; i < lnum_types; i++)
            {
                if (str == ltype_names[i])
                    return i;
            }

            return -1;

        }

        int add_type(string str)
        {
            if (str.ToUpper() == Constants.STANDARD_TYPE)
                str = Constants.STANDARD_TYPE;
            int iType = get_type(str);
            if (iType == -1)
            {
                ltype_names[lnum_types] = str;
                iType = lnum_types;
                lnum_types++;
            }
            return iType;
        }


         void collect_type_names_in_pl(PlNode n)

        {

            PlNode i;
            TypedList tyl;
            TokenList tl;
            string tmp = null;
            int nn;

            if (null == n)
            {
                return;
            }

            switch (n.connective)
            {
                case ALL:
                case EX:
                    for (tyl = n.parse_vars; tyl != null; tyl = tyl.next)
                    {
                        if (tyl.type.next != null)
                        {
                            tmp = EITHER_STR;
                            for (tl = tyl.type; tl != null; tl = tl.next)
                            {
                                tmp = tmp + CONNECTOR + tl.item;
                            }
                        }
                        else
                        {
                            tmp = tyl.type.item;
                        }
                        tyl.n = add_type(tmp);
                        /*
                        if ((nn = get_type(tmp)) == -1)
                        {
                            tyl.n = lnum_types;
                            ltype_names[lnum_types++] = tmp;
                        }
                        else
                        {
                            tyl.n = nn;
                        }
                        */
                        //free(tmp);
                        tmp = null;
                    }
                    collect_type_names_in_pl(n.sons);
                    break;
                case AND:
                case OR:
                    for (i = n.sons; i != null; i = i.next)
                    {
                        collect_type_names_in_pl(i);
                    }
                    break;
                case NOT:
                    collect_type_names_in_pl(n.sons);
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                case WHEN:
                    collect_type_names_in_pl(n.sons);
                    collect_type_names_in_pl(n.sons.next);
                    break;
                default:
                    break;
            }

        }


         void make_either_ty(TypedList tyl)

        {

            TokenList i;

            if (lnum_either_ty[tyl.n] > 0)
            {
                return;
            }

            for (i = tyl.type; i != null; i = i.next)
            {
                leither_ty[tyl.n, lnum_either_ty[tyl.n]++] = get_type(i.item);
            }

        }




         void make_either_ty_in_pl(PlNode n)

        {

            PlNode i;
            TypedList tyl;

            if (null == n)
            {
                return;
            }

            switch (n.connective)
            {
                case ALL:
                case EX:
                    for (tyl = n.parse_vars; tyl != null; tyl = tyl.next)
                    {
                        make_either_ty(tyl);
                    }
                    make_either_ty_in_pl(n.sons);
                    break;
                case AND:
                case OR:
                    for (i = n.sons; i != null; i = i.next)
                    {
                        make_either_ty_in_pl(i);
                    }
                    break;
                case NOT:
                    make_either_ty_in_pl(n.sons);
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                case WHEN:
                    make_either_ty_in_pl(n.sons);
                    make_either_ty_in_pl(n.sons.next);
                    break;
                default:
                    break;
            }

        }




         void normalize_tyl_in_pl(PlNode n)

        {

            PlNode i;
            TypedList tyl;
            PlNode tmp_pl = null, sons, p_pl;
            TokenList tmp_tl, tl;


            if (null == n)
            {
                return;
            }

            switch (n.connective)
            {
                case ALL:
                case EX:
                    /* we need to make a sequence of quantifiers ( .sons ...)
                     * out of the given sequence of TypedList  elements,
                     * with connected type names, var - name in TokenList
                     * and KEEPING THE SAME ORDERING !!
                     */
                    if (null == n.parse_vars)
                    {
                        FFUtilities.Write("\n\nquantifier without argument !! check input files.\n\n");
                        Exit(1); break;
                    }
                    tmp_tl = new TokenList();
                    tmp_tl.next = new TokenList();
                    tmp_tl.item = n.parse_vars.name;
                    if (n.parse_vars.type.next != null)
                    {
                        tmp_tl.next.item = EITHER_STR;
                        for (tl = n.parse_vars.type; tl != null; tl = tl.next)
                        {
                            tmp_tl.next.item += CONNECTOR;
                            tmp_tl.next.item += tl.item;
                        }
                    }
                    else
                    {
                        tmp_tl.next.item = n.parse_vars.type.item;
                    }
                    n.atom = tmp_tl;
                    /* now add list of sons
                     */
                    sons = n.sons;
                    p_pl = n;
                    for (tyl = n.parse_vars.next; tyl != null; tyl = tyl.next)
                    {
                        tmp_tl = new TokenList();
                        tmp_tl.next = new TokenList();
                        tmp_tl.item = tyl.name;
                        if (tyl.type.next != null)
                        {
                            tmp_tl.next.item = EITHER_STR;
                            for (tl = tyl.type; tl != null; tl = tl.next)
                            {
                                tmp_tl.next.item += CONNECTOR;
                                tmp_tl.next.item += tl.item;
                            }
                        }
                        else
                        {
                            tmp_tl.next.item = tyl.type.item;
                        }
                        tmp_pl = new PlNode(n.connective);
                        tmp_pl.atom = tmp_tl;
                        p_pl.sons = tmp_pl;
                        p_pl = tmp_pl;
                    }
                    /* remove typed-list-of info
                     */
                    //free_TypedList(n.parse_vars);
                    n.parse_vars = null;
                    /* the last son in list takes over .sons
                     */
                    p_pl.sons = sons;
                    /* normalize this sons and get out
                     */
                    normalize_tyl_in_pl((p_pl.sons));
                    break;
                case AND:
                case OR:
                    for (i = n.sons; i != null; i = i.next)
                    {
                        normalize_tyl_in_pl(i);
                    }
                    break;
                case NOT:
                    normalize_tyl_in_pl((n.sons));
                    break;
                case ATOM:
                case TRU:
                case FAL:
                    break;
                case WHEN:
                    normalize_tyl_in_pl((n.sons));
                    normalize_tyl_in_pl((n.sons.next));
                    break;
                default:
                    break;
            }

        }


        //this is the original implementation of Joerg, extracted from the function.
        //it does not seem to fit what we need, so I am reimplementing
        public bool[,] CreateTypeMatrixOriginal()
        {
            bool[,] m = new bool[lnum_types, lnum_types];
            int i, j, k, std;
            TypedList tyl;
            /* now, compute the transitive closure of all type inclusions.
             * first initialize the matrix.
             */
            for (i = 0; i < lnum_types; i++)
            {
                for (j = 0; j < lnum_types; j++)
                {
                    m[i, j] = (i == j ? true : false);
                }
            }
            std = -1;
            for (i = 0; i < lnum_types; i++)
            {
                if (ltype_names[i].ToUpper() == STANDARD_TYPE)
                {
                    std = i;
                    break;
                }
            }
            for (i = 0; i < lnum_types; i++)
            {
                m[i, std] = true;/* all types are subtypes of OBJECT */
            }
            for (tyl = FF.Parsing.gparse_types; tyl != null; tyl = tyl.next)
            {
                /* all inclusions as are defined in domain file
                 */
                int iType = get_type(tyl.name);
                m[iType, tyl.n] = true;
            }
            /* compute transitive closure on inclusions matrix
             */
            for (j = 0; j < lnum_types; j++)
            {
                for (i = 0; i < lnum_types; i++)
                {
                    if (i != j)
                    {
                        if (m[i, j])
                        {
                            for (k = 0; k < lnum_types; k++)
                            {
                                if (j != k && i != k)
                                {
                                    if (m[j, k])
                                    {
                                        m[i, k] = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            /* union types are subsets of all those types that contain all
             * their components, and 
             * all component types are subsets of the either type !
             */
            for (i = 0; i < lnum_types; i++)
            {
                if (lnum_either_ty[i] < 2) continue;
                for (j = 0; j < lnum_types; j++)
                {
                    if (j == i) continue;
                    /* get supertypes of all component types
                     */
                    for (k = 0; k < lnum_either_ty[i]; k++)
                    {
                        if (!m[leither_ty[i, k], j]) break;
                    }
                    if (k < lnum_either_ty[i]) continue;
                    m[i, j] = true;
                    /* make components subtypes of either type
                     */
                    for (k = 0; k < lnum_either_ty[i]; k++)
                    {
                        int iSub = leither_ty[i, k];
                        if (iSub != std)
                            m[iSub, i] = true;
                    }
                }
            }
            /* and again, compute transitive closure on inclusions matrix.
             * I guess, this won't change anything (?), but it also won't need
             * any remarkable computation time, so why should one think about it ?
             */
            //GUY: this seems incorrect. Example: let us assume two eithers:
            //EITHER t3 t2 t1
            //EITHER t4 t2 t1
            //from the above t2 is the child of the two eithers
            //but t4 is the child of t2, hence, t4 is the child of the first either

            for (j = 0; j < lnum_types; j++)
            {
                for (i = 0; i < lnum_types; i++)
                {
                    if (m[i, j])
                    {
                        for (k = 0; k < lnum_types; k++)
                        {
                            if (m[j, k])
                            {
                                if (!m[i, k])
                                    m[i, k] = true;
                            }
                        }
                    }
                }
            }
            return m;
        }


        //this implementation relies ONLY on the either's
        //EITHER t1 t2 t3 => m[t1,t2], m[t1,t3], m[t2,t3]
        public bool[,] CreateTypeMatrix()
        {
            bool[,] m = new bool[lnum_types, lnum_types];
            int i, j, k, std;
            TypedList tyl;
            /* now, compute the transitive closure of all type inclusions.
             * first initialize the matrix.
             */
            for (i = 0; i < lnum_types; i++)
            {
                for (j = 0; j < lnum_types; j++)
                {
                    m[i, j] = (i == j ? true : false);
                }
            }
            std = -1;
            for (i = 0; i < lnum_types; i++)
            {
                if (ltype_names[i].ToUpper() == STANDARD_TYPE)
                {
                    std = i;
                    break;
                }
            }
            for (i = 0; i < lnum_types; i++)
            {
                m[i, std] = true;/* all types are subtypes of OBJECT */
            }

            /* union types are subsets of all those types that contain all
             * their components, and 
             * all component types are subsets of the either type !
             */
            for (i = 0; i < lnum_types; i++)
            {
                for (k = 0; k < lnum_either_ty[i] - 1; k++)
                {
                    int iSubType = leither_ty[i,k];
                    for (j = k + 1; j < lnum_either_ty[i]; j++)
                    {
                        int iSuperType = leither_ty[i,j];
                        //EITHER t1 t2 => m[t1,t2] = true
                        m[iSubType,iSuperType] = true;
                    }
                    //all component types are subsets of the either type
                    m[iSubType, i] = true;
                }

            }
            
            return m;
        }


        public  void build_orig_constant_list()

        {

            string tmp = null;
            TypedList tyl;
            TypedListList tyll;
            TokenList tl, p_tl, tmp_tl;
            PlOperator po;

            int i, j, k, n, std;


            FactList fl, p_fl;

            lnum_types = 0;

            add_type(STANDARD_TYPE);

            for (tyl = FF.Parsing.gparse_types; tyl != null; tyl = tyl.next)
            {
                add_type(tyl.name);
                /*
                if (get_type(tyl.name) == -1)
                {
                    ltype_names[lnum_types++] = tyl.name;
                }
                */
                if (tyl.type.next != null)
                {
                    tmp = EITHER_STR;

                    for (tl = tyl.type; tl != null; tl = tl.next)
                    {
                        tmp = tmp + CONNECTOR + tl.item;
                    }
                }
                else
                {
                    tmp = tyl.type.item;
                }
                tyl.n = add_type(tmp); 
                /*
                if ((n = get_type(tmp)) == -1)
                {
                    tyl.n = lnum_types;
                    ltype_names[lnum_types++] = tmp;
                }
                else
                {
                    tyl.n = n;
                }
                */
                //free(tmp);
                tmp = null;
            }

            for (tyl = FF.Parsing.gparse_constants; tyl != null; tyl = tyl.next)
            {
                if (tyl.type.next != null)
                {

                    tmp = EITHER_STR;
                    for (tl = tyl.type; tl != null; tl = tl.next)
                    {
                        tmp = tmp + CONNECTOR + tl.item;
                    }
                }
                else
                {
                    tmp = tyl.type.item;
                }
                tyl.n = add_type(tmp);
                /*
                if ((n = get_type(tmp)) == -1)
                {
                    tyl.n = lnum_types;
                    ltype_names[lnum_types++] = tmp;
                }
                else
                {
                    tyl.n = n;
                }
                */
                //free(tmp);
                tmp = null;
            }

            for (tyl = FF.Parsing.gparse_objects; tyl != null; tyl = tyl.next)
            {
                if (tyl.type.next != null)
                {

                    tmp = EITHER_STR;
                    for (tl = tyl.type; tl != null; tl = tl.next)
                    {
                        tmp = tmp + CONNECTOR + tl.item;
                    }
                }
                else
                {
                    tmp = tyl.type.item;
                }
                tyl.n = add_type(tmp);
                /*
                if ((n = get_type(tmp)) == -1)
                {
                    tyl.n = lnum_types;
                    ltype_names[lnum_types++] = tmp;
                }
                else
                {
                    tyl.n = n;
                }
                */
                //free(tmp);
                tmp = null;
            }

            for (tyll = FF.Parsing.gparse_predicates; tyll != null; tyll = tyll.next)
            {
                for (tyl = tyll.args; tyl != null; tyl = tyl.next)
                {
                    if (tyl.type.next != null)
                    {

                        tmp = EITHER_STR;
                        for (tl = tyl.type; tl != null; tl = tl.next)
                        {
                            tmp = tmp + CONNECTOR + tl.item;
                        }
                    }
                    else
                    {
                        tmp = tyl.type.item;
                    }
                    tyl.n = add_type(tmp);
                    /*
                    if ((n = get_type(tmp)) == -1)
                    {
                        tyl.n = lnum_types;
                        ltype_names[lnum_types++] = tmp;
                    }
                    else
                    {
                        tyl.n = n;
                    }
                    */
                    //free(tmp);
                    tmp = null;
                }
            }

            collect_type_names_in_pl(FF.Parsing.gorig_goal_facts);

            for (po = FF.Parsing.gloaded_ops; po != null; po = po.next)
            {
                collect_type_names_in_pl(po.preconds);
                collect_type_names_in_pl(po.effects);
                for (tyl = po.parse_params; tyl != null; tyl = tyl.next)
                {
                    if (tyl.type.next != null)
                    {

                        tmp = EITHER_STR;
                        for (tl = tyl.type; tl != null; tl = tl.next)
                        {
                            tmp = tmp + CONNECTOR + tl.item;
                        }
                    }
                    else
                    {
                        tmp = tyl.type.item;
                    }
                    tyl.n = add_type(tmp);
                    /*
                    if ((n = get_type(tmp)) == -1)
                    {
                        tyl.n = lnum_types;
                        ltype_names[lnum_types++] = tmp;
                    }
                    else
                    {
                        tyl.n = n;
                    }
                    */
                    //free(tmp);
                    tmp = null;
                }
            }


            /* now get the numbers of all composed either types
             */
            for (i = 0; i < lnum_types; i++)
            {
                lnum_either_ty[i] = 0;
            }
            for (tyl = FF.Parsing.gparse_types; tyl != null; tyl = tyl.next)
            {
                make_either_ty(tyl);
            }
            for (tyl = FF.Parsing.gparse_constants; tyl != null; tyl = tyl.next)
            {
                make_either_ty(tyl);
            }
            for (tyl = FF.Parsing.gparse_objects; tyl != null; tyl = tyl.next)
            {
                make_either_ty(tyl);
            }
            for (tyll = FF.Parsing.gparse_predicates; tyll != null; tyll = tyll.next)
            {
                for (tyl = tyll.args; tyl != null; tyl = tyl.next)
                {
                    make_either_ty(tyl);
                }
            }
            make_either_ty_in_pl(FF.Parsing.gorig_goal_facts);
            for (po = FF.Parsing.gloaded_ops; po != null; po = po.next)
            {
                make_either_ty_in_pl(po.preconds);
                make_either_ty_in_pl(po.effects);
                for (tyl = po.parse_params; tyl != null; tyl = tyl.next)
                {
                    make_either_ty(tyl);
                }
            }

            bool[,] m = CreateTypeMatrix();

            /* now build FactList of ALL  constant . type   pairs.
             * for each constant / object, let it appear separately
             * for each type it is a member of; compute type
             * membership based on propagating constants / objects
             * through inclusions matrix.
             *
             * this might make the same pair appear doubly, if an object
             * is declared in type T as well as in some supertype T'.
             * such cases will be filtered out in string collection.
             */
            for (tyl = FF.Parsing.gparse_constants; tyl != null; tyl = tyl.next)
            {
                fl = new FactList();
                fl.item = new TokenList();
                fl.item.next = new TokenList();
                fl.item.item = tyl.name;
                if (tyl.type.next != null)
                {

                    fl.item.next.item = EITHER_STR;
                    for (tl = tyl.type; tl != null; tl = tl.next)
                    {
                        fl.item.next.item += CONNECTOR;
                        fl.item.next.item += tl.item;
                    }
                }
                else
                {
                    fl.item.next.item = tyl.type.item;
                }
                fl.next = FF.DP.gorig_constant_list;
                FF.DP.gorig_constant_list = fl;
                /* now add constant to all supertypes
                 */
                n = get_type(fl.item.next.item);
                for (i = 0; i < lnum_types; i++)
                {
                    if (i == n || !m[n, i]) 
                        continue;
                    fl = new FactList();
                    fl.item = new TokenList();
                    fl.item.next = new TokenList();
                    fl.item.item = tyl.name;
                    fl.item.next.item = ltype_names[i];
                    fl.next = FF.DP.gorig_constant_list;
                    FF.DP.gorig_constant_list = fl;
                }
            }
            for (tyl = FF.Parsing.gparse_objects; tyl != null; tyl = tyl.next)
            {
                fl = new FactList();
                fl.item = new TokenList();
                fl.item.next = new TokenList();
                fl.item.item = tyl.name;
                if (tyl.type.next != null)
                {

                    fl.item.next.item = EITHER_STR;
                    for (tl = tyl.type; tl != null; tl = tl.next)
                    {
                        fl.item.next.item += CONNECTOR;
                        fl.item.next.item += tl.item;
                    }
                }
                else
                {
                    fl.item.next.item = tyl.type.item;
                }
                fl.next = FF.DP.gorig_constant_list;
                FF.DP.gorig_constant_list = fl;
                /* now add constant to all supertypes
                 */
                n = get_type(fl.item.next.item);
                for (i = 0; i < lnum_types; i++)
                {
                    if (i == n ||
                     !m[n, i]) continue;
                    fl = new FactList();
                    fl.item = new TokenList();
                    fl.item.next = new TokenList();
                    fl.item.item = tyl.name;
                    fl.item.next.item = ltype_names[i];
                    fl.next = FF.DP.gorig_constant_list;
                    FF.DP.gorig_constant_list = fl;
                }
            }


            /* now, normalize all typed-list-of  s in domain and problem def,
             * i.e., in all PlNode quantifiers and in op parameters
             *
             * at the same time, remove typed-listof structures in these defs
             */
            normalize_tyl_in_pl(FF.Parsing.gorig_goal_facts);
            for (po = FF.Parsing.gloaded_ops; po != null; po = po.next)
            {
                normalize_tyl_in_pl(po.preconds);
                normalize_tyl_in_pl(po.effects);
                /* be careful to maintain parameter ordering !
                 */
                if (null == po.parse_params)
                {
                    continue;/* no params at all */
                }
                fl = new FactList();
                fl.item = new TokenList();
                fl.item.next = new TokenList();
                fl.item.item = po.parse_params.name;
                if (po.parse_params.type.next != null)
                {
                    fl.item.next.item = EITHER_STR;
                    for (tl = po.parse_params.type; tl != null; tl = tl.next)
                    {
                        fl.item.next.item += CONNECTOR;
                        fl.item.next.item += tl.item;

                    }
                }
                else
                {
                    fl.item.next.item = po.parse_params.type.item;
                }
                po.parameters = fl;
                p_fl = fl;
                for (tyl = po.parse_params.next; tyl != null; tyl = tyl.next)
                {
                    fl = new FactList();
                    fl.item = new TokenList();
                    fl.item.next = new TokenList();
                    fl.item.item = tyl.name;
                    if (tyl.type.next != null)
                    {
                        fl.item.next.item = EITHER_STR;
                        for (tl = tyl.type; tl != null; tl = tl.next)
                        {
                            fl.item.next.item += CONNECTOR;
                            fl.item.next.item += tl.item;
                        }
                    }
                    else
                    {
                        fl.item.next.item = tyl.type.item;
                    }
                    p_fl.next = fl;
                    p_fl = fl;
                }
                //free_TypedList(po.parse_params);
                po.parse_params = null;
            }


            /* finally, build  Main.DP.gpredicates_and_types  by chaining predicate names 
             * together with the names of their args' types.
             */
            for (tyll = FF.Parsing.gparse_predicates; tyll != null; tyll = tyll.next)
            {
                fl = new FactList();
                fl.item = new TokenList();
                fl.item.item = tyll.predicate;
                fl.next = FF.DP.gpredicates_and_types;
                FF.DP.gpredicates_and_types = fl;
                if (null == tyll.args) continue;
                /* add arg types; MAINTAIN ORDERING !
                 */
                fl.item.next = new TokenList();
                if (tyll.args.type.next != null)
                {
                    fl.item.next.item = EITHER_STR;
                    for (tl = tyll.args.type; tl != null; tl = tl.next)
                    {
                        fl.item.next.item += CONNECTOR;
                        fl.item.next.item += tl.item;

                    }
                }
                else
                {
                    fl.item.next.item = tyll.args.type.item;
                }
                p_tl = fl.item.next;
                for (tyl = tyll.args.next; tyl != null; tyl = tyl.next)
                {
                    tmp_tl = new TokenList();
                    if (tyl.type.next != null)
                    {
                        tmp_tl.item = EITHER_STR;
                        for (tl = tyl.type; tl != null; tl = tl.next)
                        {
                            tmp_tl.item += CONNECTOR;
                            tmp_tl.item += tl.item;
                        }
                    }
                    else
                    {
                        tmp_tl.item = tyl.type.item;
                    }
                    p_tl.next = tmp_tl;
                    p_tl = tmp_tl;
                }
            }


            /* now get rid of remaining typed-list-of parsing structures
             */
            //free_TypedList(FF.Parsing.gparse_types);
            FF.Parsing.gparse_types = null;
            //free_TypedList(FF.Parsing.gparse_constants);
            FF.Parsing.gparse_constants = null;
            //free_TypedList(FF.Parsing.gparse_objects);
            FF.Parsing.gparse_objects = null;
            //free_TypedListList(FF.Parsing.gparse_predicates);
            FF.Parsing.gparse_predicates = null;

        }

















        /* ADL syntax test - and normalization (AND s etc.)
         */












        public  bool make_adl_domain()

        {

            PlOperator i;
            FactList ff;

            if (gcmd_line.display_info == 101)
            {
                FFUtilities.Write("\noriginal problem parsing is:\n");
                FFUtilities.Write("\nobjects:");
                for (ff = FF.DP.gorig_constant_list; ff != null; ff = ff.next)
                {
                    FFUtilities.Write("\n" + ff.item.item + "," + ff.item.next.item);
                }
                FFUtilities.Write("\n\ninitial state:\n");
                Output.print_PlNode(FF.Parsing.gorig_initial_facts, 0);
                FFUtilities.Write("\n\ngoal state:\n");
                Output.print_PlNode(FF.Parsing.gorig_goal_facts, 0);
                FFUtilities.Write("\n\nops:");
                Output.print_plops(FF.Parsing.gloaded_ops);
            }

            if( !make_conjunction_of_atoms(FF.Parsing.gorig_initial_facts))
            {
                FFUtilities.Write("\nillegal initial state");
                return false;
            }

            if( null == FF.Parsing.gorig_goal_facts)
            {
                FF.Parsing.gorig_goal_facts = new PlNode(TRU);
            }

            if( !is_wff(FF.Parsing.gorig_goal_facts))
            {
                FFUtilities.Write("\nillegal goal formula");
                print_PlNode(FF.Parsing.gorig_goal_facts, 0);
                return false;
            }

            for (i = FF.Parsing.gloaded_ops; i != null ; i = i.next)
            {
                if( null == i.preconds)
                {
                    i.preconds = new PlNode(TRU);
                }
                if(!is_wff(i.preconds))
                {
                    FFUtilities.Write("\nop %s has illegal precondition", i.name);
                    return false;
                }
                if(!make_effects((i.effects)))
                {
                    FFUtilities.Write("\nop %s has illegal effects", i.name);
                    return false;
                }
            }

            if (gcmd_line.display_info == 102)
            {
                FFUtilities.Write("\nfinal ADL representation is:\n");
                FFUtilities.Write("\nobjects:");
                for (ff = FF.DP.gorig_constant_list; ff != null; ff = ff.next)
                {
                    FFUtilities.Write("\n%s : %s", ff.item.item, ff.item.next.item);
                }
                FFUtilities.Write("\n\ninitial state:\n");
                print_PlNode(FF.Parsing.gorig_initial_facts, 0);
                FFUtilities.Write("\n\ngoal formula:\n");
                print_PlNode(FF.Parsing.gorig_goal_facts, 0);
                FFUtilities.Write("\n\nops:");
                print_plops(FF.Parsing.gloaded_ops);
            }

            return true;

        }



        public  bool make_conjunction_of_atoms(PlNode n)

        {

            PlNode tmp, i, p, m;

            if( null == n)
            {
                return true;
            }

            if (n.connective != AND)
            {
                switch (n.connective)
                {
                    case ATOM:
                        tmp = new PlNode(ATOM);
                        tmp.atom = n.atom;
                        n.atom = null;
                        n.connective = AND;
                        n.sons = tmp;
                        return true;
                    case NOT:
                        //free_PlNoden;
                        n = null;
                        return true;
                    default:
                        return false;
                }
            }

            p = null;
            for (i = n.sons; i != null ; i = i.next)
            {
                switch (i.connective)
                {
                    case ATOM:
                        break;
                    case NOT:
                        if (p != null)
                        {
                            p.next = i.next;
                        }
                        else
                        {
                            n.sons = i.next;
                        }
                        m = i.next;
                        i.next = null;
                        //free_PlNode(i);
                        i = m;
                        break;
                    default:
                        return false;
                }
                p = i;
                if( null == i) break;
            }

            return true;

        }



        public  bool is_wff(PlNode n)
        {
            PlNode i;

            if( null == n)
            {
                return false;
            }

            switch (n.connective)
            {
                case ALL:
                case EX:
                    if( null == (n.atom) ||
                     n.atom.next == null ||
                     n.atom.next.next != null) //potnetial bug
                    {
                        return false;
                    }
                    return is_wff(n.sons);
                case AND:
                case OR:
                    for (i = n.sons; i != null ; i = i.next)
                    {
                        if( !is_wff(i))
                        {
                            return false;
                        }
                    }
                    return true;
                case NOT:
                    return is_wff(n.sons);
                case ATOM:
                    if( null == (n.atom) ||
                     n.sons != null)
                    {
                        return false;
                    }
                    return true;
                case TRU:
                case FAL:
                    if (n.sons != null)
                    {
                        return false;
                    }
                    return true;
                default:
                    return false;
            }

        }



        public  bool make_effects(PlNode n)
        {

            PlNode tmp, i, literals, j, k, next;
            int m = 0;

            if (n.connective != AND)
            {
                if( !is_eff_literal(n) &&
                 n.connective != ALL &&
                 n.connective != WHEN)
                {
                    return false;
                }
                tmp = new PlNode(n.connective);
                tmp.atom = n.atom;
                tmp.sons = n.sons;
                n.connective = AND;
                n.sons = tmp;
            }

            for (i = n.sons; i != null ; i = i.next)
            {
                if (is_eff_literal(i))
                {
                    m++;
                    continue;
                }
                if (i.connective == AND)
                {
                    for (j = i.sons; j != null; j = j.next)
                    {
                        if( !is_eff_literal(j))
                        {
                            return false;
                        }
                        m++;
                    }
                    continue;
                }
                if (i.connective == ALL)
                {
                    for (j = i.sons; j != null && j.connective == ALL; j = j.sons)
                    {
                        if( null == j.atom ||
                             j.atom.next == null ||
                             j.atom.next.next != null) //potential BUGBUG
                        {
                            return false;
                        }
                    }
                    if( null == j)
                    {
                        return false;
                    }
                    if (is_eff_literal(j))
                    {
                        tmp = new PlNode(AND);
                        for (k = i; k.sons.connective == ALL; k = k.sons) ;
                        k.sons = tmp;
                        tmp.sons = j;
                        j = tmp;
                    }
                    if (j.connective == AND)
                    {
                        for (k = j.sons; k != null; k = k.next)
                        {
                            if(!is_eff_literal(k))
                            {
                                return false;
                            }
                        }
                        tmp = new PlNode(WHEN);
                        for (k = i; k.sons.connective == ALL; k = k.sons) ;
                        k.sons = tmp;
                        tmp.sons = new PlNode(TRU);
                        tmp.sons.next = j;
                        continue;
                    }
                    if (j.connective != WHEN)
                    {
                        return false;
                    }
                    if( null == (j.sons))
                    {
                        j.sons = new PlNode(TRU);
                    }
                    if(!is_wff(j.sons))
                    {
                        return false;
                    }
                    if(!make_conjunction_of_literals((j.sons.next)))
                    {
                        return false;
                    }
                    continue;
                }
                if (i.connective != WHEN)
                {
                    return false;
                }
                if( null == (i.sons))
                {
                    i.sons = new PlNode(TRU);
                }
                if(!is_wff(i.sons))
                {
                    return false;
                }
                if(!make_conjunction_of_literals((i.sons.next)))
                {
                    return false;
                }
            }

            if (m == 0)
            {
                return true;
            }

            tmp = new PlNode(WHEN);
            tmp.sons = new PlNode(TRU);
            literals = new PlNode(AND);
            tmp.sons.next = literals;
            tmp.next = n.sons;
            n.sons = tmp;
            i = n.sons;
            while (i.next != null)
            {
                if (is_eff_literal(i.next))
                {
                    next = i.next.next;
                    i.next.next = literals.sons;
                    literals.sons = i.next;
                    i.next = next;
                    continue;
                }
                if (i.next.connective == AND)
                {
                    next = i.next.next;
                    for (j = i.next.sons; j != null && j.next != null; j = j.next) ;
                    if (j != null)
                    {
                        j.next = literals.sons;
                        literals.sons = i.next.sons;
                    }
                    i.next = next;
                    continue;
                }
                i = i.next;
            }
            return true;

        }



        public  bool is_eff_literal(PlNode n)

        {

            if( null == n)
            {
                return false;
            }

            if (n.connective == NOT)
            {
                if( null == n.sons ||
                 n.sons.connective != ATOM ||
                 n.sons.atom == null)
                {
                    return false;
                }
                return true;
            }

            if (n.connective == ATOM)
            {
                if( null == n.atom)
                {
                    return false;
                }
                return true;
            }

            return false;

        }



        public  bool make_conjunction_of_literals(PlNode n)

        {

            PlNode tmp, i;

            if( null == n)
            {
                return false;
            }

            if (n.connective != AND)
            {
                if (n.connective == NOT)
                {
                    if( null == (n.sons) ||
                     n.sons.connective != ATOM)
                    {
                        return false;
                    }
                    tmp = new PlNode(NOT);
                    tmp.sons = n.sons;
                    n.connective = AND;
                    n.sons = tmp;
                    return true;
                }
                if (n.connective != ATOM)
                {
                    return false;
                }
                tmp = new PlNode(ATOM);
                tmp.atom = n.atom;
                n.atom = null;
                n.connective = AND;
                n.sons = tmp;
                return true;
            }

            for (i = n.sons; i != null ; i = i.next)
            {
                if(!is_eff_literal(i))
                {
                    return false;
                }
            }

            return true;

        }



    }
}
