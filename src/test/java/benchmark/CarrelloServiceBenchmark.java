package benchmark;


import controller.HomePage.CarrelloServletPackage.CarrelloService;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.openjdk.jmh.annotations.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
@State(Scope.Benchmark)
public class CarrelloServiceBenchmark {

    private CarrelloService service;
    private Utente utente;
    private Carrello carrello;

    @Setup(Level.Trial)
    public void setup() {
        service = new CarrelloService();
        utente = null; // scenario "utente null"

        Libro libro1 = new Libro();
        libro1.setIsbn("111-AAA");
        libro1.setDisponibile(true);

        RigaCarrello riga1 = new RigaCarrello();
        riga1.setLibro(libro1);
        riga1.setQuantita(1);

        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga1);

        carrello = new Carrello();
        carrello.setRigheCarrello(righe);
    }

    @Benchmark
    public void whenUserIsNull_processesCartNormally() {
        service.preparaDati(utente, carrello);
    }
}

