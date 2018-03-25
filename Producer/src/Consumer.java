import java.util.LinkedList;
import java.util.List;

public class Consumer implements Runnable {

    public static void main(String[] args) {
        List<String> msgs = new LinkedList<>();
        Consumer c = new Consumer(1, msgs);

        for (int i = 1; i <= 2; i++) {
            Thread t = new Thread(new Producer(i, msgs));
            t.start();
        }

        c.run();
    }

    private static final int Interval = 1000;
    private int id;
    private List<String> msgs;

    public Consumer(int id, List<String> msgs) {
        this.id = id;
        this.msgs = msgs;
    }

    @Override
    public void run() {
        while (true) {
            if (msgs.size() > 0) {
                System.out.printf("C[%d] current message size: %d.\n", id, msgs.size());
                System.out.printf("C[%d] has consumed an item.\n", id);
                String m = msgs.remove(0);
                System.out.println("C[%d] the message is: " + m);
            }

            try {
                Thread.sleep(Interval);
            } catch (InterruptedException e) {
                e.printStackTrace();
                return;
            }
        }
    }

}