package benchmark;

import model.carrelloService.AggiornaCarrelloService;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Benchmark JMH per misurare il tempo di aggiornamento
 * della quantità di una riga del carrello dato un ISBN.
 *
 * Nessun accesso al database, nessuna servlet, nessun Mockito:
 * misuriamo solo la logica Java pura di AggiornaCarrelloService.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 10, time = 1)
@Fork(1)
public class AggiornaCarrelloServiceBenchmark {

    @State(Scope.Benchmark)
    public static class BenchmarkState {

        AggiornaCarrelloService service;

        Carrello carrello;
        String targetIsbn;
        int nuovaQuantita;

        @Setup(Level.Trial)
        public void setUp() {
            service = new AggiornaCarrelloService();

            carrello = new Carrello();

            List<RigaCarrello> righe = new ArrayList<>();
            carrello.setRigheCarrello(righe);

            // Configuriamo un carrello "tipo"
            // es. 50 righe, l'ultima con l'ISBN bersaglio (worst case di ricerca)
            int numeroRighe = 50;
            targetIsbn = "TARGET-ISBN";
            nuovaQuantita = 5;

            for (int i = 0; i < numeroRighe; i++) {
                RigaCarrello riga = new RigaCarrello();

                // idCarrello valido
                riga.setIdCarrello("CARR002");

                // Libro coerente con le specifiche JML
                Libro libro = new Libro();
                if (i == numeroRighe - 1) {
                    // l'ultima riga ha l'ISBN bersaglio
                    libro.setIsbn(targetIsbn);
                } else {
                    libro.setIsbn("ISBN-" + i);
                }
                libro.setTitolo("Titolo " + i);
                libro.setPrezzo(10.0 + i);
                libro.setSconto(10);
                libro.setAutori(new ArrayList<>());

                riga.setLibro(libro);

                // quantita >= 0
                riga.setQuantita(1);

                righe.add(riga);
            }
        }
    }

    @Benchmark
    public void benchmarkAggiornaQuantita(BenchmarkState state, Blackhole bh) {
        boolean found = state.service.aggiornaQuantita(
                state.carrello,
                state.targetIsbn,
                state.nuovaQuantita
        );
        bh.consume(found);
        bh.consume(state.carrello);
    }
}
