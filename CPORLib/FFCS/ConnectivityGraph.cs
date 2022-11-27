using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{

    public class ConnectivityGraph
    {



        /* one ops (actions) array ...
         */
        public InitializedArray<OpConn> gop_conn;
        public int gnum_op_conn;



        /* one effects array ...
         */
        public InitializedArray<EfConn> gef_conn;
        public int gnum_ef_conn;



        /* one facts array.
         */
        public InitializedArray<FtConn> gft_conn;
        public int gnum_ft_conn;



    }


}
