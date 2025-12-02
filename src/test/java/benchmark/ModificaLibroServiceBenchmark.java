package benchmark;

import controller.admin.gestisciProdotti.ModificaLibro.ModificaLibroService;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Fork(2)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
public class ModificaLibroServiceBenchmark {

    @State(Scope.Benchmark)
    public static class ServiceState {

        @Param({"10", "100", "1000"})
        public int datasetSize; // numero di sedi/reparti totali

        ModificaLibroService service;
        String isbn;

        List<Sede> sedi;
        List<Sede> sediNonPresenti;
        List<Reparto> reparti;
        List<Reparto> repartiNonPresenti;

        @Setup(Level.Trial)
        public void setUp() {
            isbn = "978-0-596-00712-6";

            // Libro finto
            Libro libro = new Libro();
            libro.setIsbn(isbn);
            libro.setTitolo("Design Patterns");

            // Liste che simulano i dati che verrebbero dal DB
            List<Sede> tutteLeSedi = new ArrayList<>();
            List<Sede> sediPresenti = new ArrayList<>();

            List<Reparto> tuttiIReparti = new ArrayList<>();
            List<Reparto> repartiPresenti = new ArrayList<>();

            // POPOLAMENTO DATI (arricchimento):
            // - datasetSize sedi (0..datasetSize-1)
            // - datasetSize reparti (0..datasetSize-1)
            // - metà "presenti", metà "non presenti"
            for (int i = 0; i < datasetSize; i++) {
                Sede s = new Sede();
                s.setIdSede(i);
                s.setCitta("Citta " + i);
                s.setVia("Via " + i);
                s.setCivico(i);
                s.setCap(String.format("%05d", i));

                tutteLeSedi.add(s);
                if (i % 2 == 0) { // metà presenti
                    sediPresenti.add(s);
                }

                Reparto r = new Reparto();
                r.setIdReparto(i);
                r.setNome("Reparto " + i);
                r.setDescrizione("Descrizione " + i);

                tuttiIReparti.add(r);
                if (i % 2 == 0) {
                    repartiPresenti.add(r);
                }
            }

            // DAO finti: nessun accesso a DB, usano solo le liste sopra
            FakeLibroDAO fakeLibroDAO = new FakeLibroDAO(libro, sediPresenti, repartiPresenti);
            FakeSedeDAO fakeSedeDAO = new FakeSedeDAO(tutteLeSedi);
            FakeRepartoDAO fakeRepartoDAO = new FakeRepartoDAO(tuttiIReparti);

            // Service costruito con i DAO finti
            service = new ModificaLibroService(fakeLibroDAO, fakeSedeDAO, fakeRepartoDAO);

            // Liste che verranno riempite a ogni esecuzione del benchmark
            sedi = new ArrayList<>();
            sediNonPresenti = new ArrayList<>();
            reparti = new ArrayList<>();
            repartiNonPresenti = new ArrayList<>();
        }

        // --- DAO finti interni allo state ---

        static class FakeLibroDAO extends LibroDAO {

            private final Libro libro;
            private final List<Sede> sediPresenti;
            private final List<Reparto> repartiPresenti;

            FakeLibroDAO(Libro libro,
                         List<Sede> sediPresenti,
                         List<Reparto> repartiPresenti) {
                this.libro = libro;
                this.sediPresenti = sediPresenti;
                this.repartiPresenti = repartiPresenti;
            }

            @Override
            public Libro doRetrieveById(String isbn) {
                return libro;
            }

            @Override
            public List<Sede> getPresenzaSede(String isbn) {
                return sediPresenti;
            }

            @Override
            public List<Reparto> getAppartenenzaReparto(String isbn) {
                return repartiPresenti;
            }
        }

        static class FakeSedeDAO extends SedeDAO {

            private final List<Sede> tutteLeSedi;

            FakeSedeDAO(List<Sede> tutteLeSedi) {
                this.tutteLeSedi = tutteLeSedi;
            }

            @Override
            public List<Sede> doRetrivedAll() {
                return tutteLeSedi;
            }
        }

        static class FakeRepartoDAO extends RepartoDAO {

            private final List<Reparto> tuttiIReparti;

            FakeRepartoDAO(List<Reparto> tuttiIReparti) {
                this.tuttiIReparti = tuttiIReparti;
            }

            @Override
            public List<Reparto> doRetrivedAll() {
                return tuttiIReparti;
            }
        }
    }

    @Benchmark
    public void benchmarkPreparaDati(ServiceState state, Blackhole bh) {
        Libro libro = state.service.preparaDati(
                state.isbn,
                state.sedi,
                state.sediNonPresenti,
                state.reparti,
                state.repartiNonPresenti
        );

        // Consumiamo i risultati per evitare ottimizzazioni del JIT
        bh.consume(libro);
        bh.consume(state.sedi);
        bh.consume(state.sediNonPresenti);
        bh.consume(state.reparti);
        bh.consume(state.repartiNonPresenti);
    }
}