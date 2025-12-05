package benchmark;

import controller.utente.ordine.RiepilogoOrdinePackage.RiepilogoOrdineService;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import org.openjdk.jmh.annotations.*;

import java.util.concurrent.TimeUnit;

/**
 * Benchmark che riproduce lo scenario del test:
 *
 *     testDoGet_UserIsNotAdmin()
 *
 * ma a livello di service:
 *  - utente con tipo "user" (non admin)
 *  - viene chiamato ordineDAO.doRetrieveById("123")
 *  - il risultato viene usato come Ordine nel Result
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
@State(Scope.Benchmark)
public class RiepilogoOrdineServiceNonAdminBenchmark {

    private RiepilogoOrdineService service;

    private Utente utenteNonAdmin;
    private OrdineDAO ordineDAO;
    private String idOrdine;

    @Setup(Level.Trial)
    public void setup() {
        service = new RiepilogoOrdineService();

        // --- Utente non admin ---
        utenteNonAdmin = new Utente();
        // assumo che Utente abbia setTipo(String); se non ce l'ha, vedi nota più sotto
        utenteNonAdmin.setTipo("user");

        // --- Ordine "finto" restituito dal DAO ---
        Ordine ordineFinto = new Ordine();
        // se vuoi, puoi settare qualche campo, ma non è necessario per il benchmark
        // es: ordineFinto.setId("123");

        // --- DAO finto in memoria, senza DB ---
        ordineDAO = new FakeOrdineDAO(ordineFinto);

        // idOrdine come nel test
        idOrdine = "123";
    }

    @Benchmark
    public void whenUserIsNotAdmin() {
        // misuriamo la logica:
        // - riconoscere che NON è admin
        // - chiamare ordineDAO.doRetrieveById("123")
        // - restituire il Result con l'ordine
        service.preparaDati(utenteNonAdmin, idOrdine, ordineDAO);
    }

    /**
     * Implementazione minimale di OrdineDAO che non va sul DB,
     * ma restituisce sempre lo stesso Ordine.
     *
     * Evita che il benchmark misuri accesso a DB e connessioni,
     * ci interessa solo il costo "logico" della chiamata.
     */
    private static class FakeOrdineDAO extends OrdineDAO {
        private final Ordine ordine;

        public FakeOrdineDAO(Ordine ordine) {
            this.ordine = ordine;
        }

        @Override
        public Ordine doRetrieveById(String idOrdine) {
            return ordine;
        }
    }
}
