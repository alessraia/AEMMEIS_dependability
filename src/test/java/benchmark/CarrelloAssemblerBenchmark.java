package benchmark;

import benchmark.util.CarrelloAssemblerForBenchmark;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Benchmark JMH che misura il tempo di costruzione
 * di un oggetto Carrello a partire da dati già disponibili
 * in memoria (id, totale, email, righe).
 *
 * Nessun accesso al database, nessun Mockito:
 * misuriamo solo la logica Java "pura" della creazione dell'oggetto.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 10, time = 1)
@Fork(1)
public class CarrelloAssemblerBenchmark {

    @State(Scope.Benchmark)
    public static class BenchmarkState {

        CarrelloAssemblerForBenchmark assembler;

        String idCarrello;
        double totale;
        String email;
        List<RigaCarrello> righeCarrello;

        @Setup(Level.Trial)
        public void setUp() {
            assembler = new CarrelloAssemblerForBenchmark();

            // Valori “coerenti” con l’applicazione
            idCarrello = "CARR002";          // non nullo e non vuoto
            totale = 200.0;
            email = "mario@example.com";

            righeCarrello = new ArrayList<>();

            // Simuliamo un carrello con un numero "tipico" di righe
            int numeroRighe = 5;

            for (int i = 0; i < numeroRighe; i++) {
                RigaCarrello riga = new RigaCarrello();

                //  rispettiamo il requires di setIdCarrello:
                //    idCarrello != null && !idCarrello.isEmpty()
                riga.setIdCarrello(idCarrello);

                // creiamo un Libro che rispetta le precondizioni JML dei setter
                Libro libro = new Libro();
                // isbn != null
                libro.setIsbn("ISBN-" + i);
                // titolo != null
                libro.setTitolo("Titolo " + i);
                // prezzo >= 0
                libro.setPrezzo(10.0 + i);
                // 0 <= sconto <= 100
                libro.setSconto(10);
                // autori != null (può essere lista vuota)
                libro.setAutori(new ArrayList<>());

                libro.setGenere("Genere");
                libro.setAnnoPubblicazioni("2024");
                libro.setTrama("Trama di esempio");
                libro.setImmagine("immagine.jpg");
                libro.setDisponibile(true);

                riga.setLibro(libro);

                // quantita >= 0
                riga.setQuantita(i + 1); // quantità da 1 a numeroRighe

                righeCarrello.add(riga);
            }
        }
    }

    @Benchmark
    public void benchmarkBuildCarrello(BenchmarkState state, Blackhole bh) {
        Carrello carrello = state.assembler.buildCarrello(
                state.idCarrello,
                state.totale,
                state.email,
                state.righeCarrello
        );
        bh.consume(carrello);
    }
}
