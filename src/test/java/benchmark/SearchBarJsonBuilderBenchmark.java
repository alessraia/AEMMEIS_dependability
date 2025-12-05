package benchmark;

import benchmark.util.SearchBarJsonBuilderForBenchmark;
import model.libroService.Libro;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Benchmark JMH che misura il tempo medio necessario
 * per trasformare una lista di Libro in una risposta
 * JSON come quella generata da SearchBarServlet.
 *
 * Nessuna servlet, nessun DB, nessun Mockito:
 * solo logica di costruzione del JSONArray.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 10, time = 1)
@Fork(1)
public class SearchBarJsonBuilderBenchmark {

    @State(Scope.Benchmark)
    public static class BenchmarkState {

        SearchBarJsonBuilderForBenchmark builder;
        List<Libro> risultatiRicerca;
        int maxResults;

        @Setup(Level.Trial)
        public void setUp() {
            builder = new SearchBarJsonBuilderForBenchmark();
            maxResults = 10;

            risultatiRicerca = new ArrayList<>();

            // Simuliamo una ricerca che ritorna, ad esempio, 100 libri
            int numeroLibri = 100;

            for (int i = 0; i < numeroLibri; i++) {
                Libro libro = new Libro();

                // Rispettiamo le precondizioni JML di Libro

                // isbn != null
                libro.setIsbn("ISBN-" + i);
                // titolo != null
                libro.setTitolo("Titolo " + i);
                // prezzo >= 0
                libro.setPrezzo(10.0 + i);
                // 0 <= sconto <= 100
                libro.setSconto(10);
                // autori != null (lista vuota va bene)
                libro.setAutori(new ArrayList<>());

                // gli altri campi non hanno requires specifici,
                // possono restare null o essere inizializzati se vuoi:
                // libro.setGenere("Genere");
                // libro.setAnnoPubblicazioni("2024");
                // libro.setTrama("Trama di esempio");
                // libro.setImmagine("cover" + i + ".jpg");
                // libro.setDisponibile(true);

                risultatiRicerca.add(libro);
            }
        }
    }

    /**
     * Misura il tempo di costruzione della stringa JSON
     * a partire da una lista di risultati.
     */
    @Benchmark
    public void benchmarkBuildJsonString(BenchmarkState state, Blackhole bh) {
        String json = state.builder.buildJsonString(
                state.risultatiRicerca,
                state.maxResults
        );
        bh.consume(json);
    }
}
