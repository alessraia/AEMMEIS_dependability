package benchmark;

import controller.utente.ordine.RiepilogoOrdinePackage.RiepilogoOrdineService;
import model.ordineService.OrdineDAO;
import model.utenteService.Utente;
import org.openjdk.jmh.annotations.*;

import java.util.concurrent.TimeUnit;

/**
 * Benchmark che riproduce lo scenario "testDoGet_UserIsAdmin"
 * ma a livello di service:
 *
 * - utente admin (tipo = "Gestore")
 * - il service deve riconoscere l'admin e NON interrogare il DAO
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
@State(Scope.Benchmark)
public class RiepilogoOrdineServiceBenchmark {

    private RiepilogoOrdineService service;

    private Utente utenteAdmin;
    private OrdineDAO ordineDAO;
    private String idOrdine;

    @Setup(Level.Trial)
    public void setup() {
        service = new RiepilogoOrdineService();

        // Utente admin: assumo che Utente abbia un setTipo(String)
        utenteAdmin = new Utente();
        utenteAdmin.setTipo("Gestore"); // stesso "tipo" usato nel test

        // DAO reale: in questo scenario non viene chiamato,
        // perché il service esce subito per gli admin.
        ordineDAO = new OrdineDAO();

        // idOrdine "finto" (non usato nel ramo admin)
        idOrdine = "TEST-ORDINE-ADMIN";
    }

    @Benchmark
    public void whenUserIsAdmin() {
        // misuriamo solo la logica di business:
        // riconoscere l'admin ed evitare la query al DAO
        service.preparaDati(utenteAdmin, idOrdine, ordineDAO);
    }
}

