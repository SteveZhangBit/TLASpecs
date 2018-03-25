import java.util.List;

public class Producer implements Runnable {

    private static final int Interval = 1000;
    /*
     * Max == 3
     */
    private static final int MaxSize = 3;
    private int id;
    /*
     * VARIABLES queue
     */
    private List<String> queue;

    /*
     * NewProducer(q) == /\ queue' = q
     */
    public Producer(int id, List<String> queue) {
        this.id = id;
        this.queue = queue;
    }

    // process producer \in Producer
    // begin
    @Override
    public void run() {
        // l1: while TRUE do
        /*
         * run_l1(self) == /\ pc[self] = "run_l1"
         *                 /\ pc' = [pc EXCEPT ![self] = "run_l2"]
         *                 /\ UNCHANGED <<queue>>
         */
        // start fragment
        while (true) {
            // end fragment
            // l2: if Len(queue) < Max then
            /*
             * run_l2(self) == /\ pc[self] = "run_l2"
             *                 /\ IF Len(queue) < Max
             *                      THEN /\ pc' = [pc EXCEPT ![self] = "run_l3"]
             *                      ELSE /\ pc' = [pc EXCEPT ![self] = "run_l1"]
             *                 /\ UNCHANGED <<queue>>
             */
            // start fragment
            if (queue.size() < MaxSize) {
                // end fragment
                System.out.printf("P[%d] produced an item.\n", id);
                // l3: queue := Append(queue, "Product");
                /*
                 * run_l3(self) == /\ pc[self] = "run_l3"
                 *                 /\ queue' = Append(queue, "Product")
                 *                 /\ pc' = [pc EXCEPT ![self] = "run_l1"]
                 */
                // start fragment
                queue.add("Product by " + id);
                // end fragment
            }
            // end if;

            try {
                Thread.sleep(Interval);
            } catch (InterruptedException e) {
                e.printStackTrace();
                return;
            }
        }
        // end while;
    }
    // end process;

}