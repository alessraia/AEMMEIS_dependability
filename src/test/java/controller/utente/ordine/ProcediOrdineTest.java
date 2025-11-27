package controller.utente.ordine;

import controller.utente.ordine.ProcediOrdine;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class ProcediOrdineTest {

    private ProcediOrdine servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private LibroDAO libroDAO;
    private SedeDAO sedeDAO;

    @BeforeEach
    void setUp() {
        servletUnderTest = new ProcediOrdine();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        libroDAO = mock(LibroDAO.class);
        sedeDAO = mock(SedeDAO.class);

        servletUnderTest.setLibroDAO(libroDAO);
        servletUnderTest.setSedeDAO(sedeDAO);
        when(sedeDAO.doRetrivedAll()).thenReturn(new ArrayList<>());
        when(libroDAO.getPresenzaSede(anyString())).thenReturn(new ArrayList<>());
        when(request.getSession()).thenReturn(session);
    }


    /**
     * Flusso principale: utente standard/premium,
     * righeDisponibili -> calcolo sedi -> forward a procediOrdine.jsp
     * ENHANCED: Aggiunto ArgumentCaptor per verificare setAttribute
     * ENHANCED: Verifica che il metodo getPresenzaSede venga chiamato (esegue il loop interno)
     */
    @Test
    void testDoGet_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setDisponibile(true);
        libro.setIsbn("123456");
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setIdCarrello("1");
        righeDisponibili.add(rigaCarrello);

        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);

        when(request.getRequestDispatcher("/WEB-INF/results/procediOrdine.jsp"))
                .thenReturn(dispatcher);

        // ArgumentCaptor per catturare la lista di sedi passata a setAttribute
        ArgumentCaptor<List<Sede>> sediCaptor = ArgumentCaptor.forClass(List.class);

        servletUnderTest.doGet(request, response);

        // Verifica che setAttribute sia stato chiamato con "sedi"
        verify(request).setAttribute(eq("sedi"), sediCaptor.capture());

        // Verifica che la lista catturata non sia null
        List<Sede> capturedSedi = sediCaptor.getValue();
        assertNotNull(capturedSedi);

        // CRUCIALE: Verifica che getPresenzaSede sia stato chiamato
        // Questo prova che il codice dentro if(!righe.isEmpty()) è stato eseguito
        verify(libroDAO).getPresenzaSede("123456");

        verify(dispatcher).forward(request, response);
    }

    /**
     * Test per righe carrello vuote - testa il boundary della condizione !righe.isEmpty()
     * NUOVO: Questo test elimina la mutazione "negated conditional" sulla linea 47
     * ENHANCED: Verifica che getPresenzaSede NON venga chiamato con carrello vuoto
     */
    @Test
    void testDoGet_EmptyCart() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        // Lista vuota - testa il caso !righe.isEmpty() == false
        List<RigaCarrello> righeVuote = new ArrayList<>();
        when(session.getAttribute("righeDisponibili")).thenReturn(righeVuote);

        when(request.getRequestDispatcher("/WEB-INF/results/procediOrdine.jsp"))
                .thenReturn(dispatcher);

        ArgumentCaptor<List<Sede>> sediCaptor = ArgumentCaptor.forClass(List.class);

        servletUnderTest.doGet(request, response);

        // Verifica setAttribute chiamato anche con carrello vuoto
        verify(request).setAttribute(eq("sedi"), sediCaptor.capture());

        List<Sede> capturedSedi = sediCaptor.getValue();
        assertNotNull(capturedSedi);

        // CRUCIALE: Verifica che getPresenzaSede NON sia stato chiamato
        // Con carrello vuoto, il blocco if(!righe.isEmpty()) NON deve essere eseguito
        verify(libroDAO, never()).getPresenzaSede(anyString());

        // Con carrello vuoto, tutte le sedi devono rimanere disponibili
        // (nessun libro da filtrare, quindi nessuna sede viene rimossa)

        verify(dispatcher).forward(request, response);
    }
}