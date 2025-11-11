import controller.utente.ordine.Pagamento;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

class PagamentoTest {

    private Pagamento servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new Pagamento();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
    }


    /**
     * Flusso principale: inserimento indirizzo corretto -> pagamentoOrdine.jsp
     */
    @Test
    void testDoGet_AddressForm_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        // Righe disponibili
        List<RigaCarrello> righe = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setIdCarrello("2");
        righe.add(rigaCarrello);  // TOT = 20
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);

        // Parametri di indirizzo
        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("Via Roma");
        when(request.getParameter("cap")).thenReturn("80100");
        when(request.getParameter("citta")).thenReturn("Napoli");

        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: errore nell'indirizzo
     * UC_RF_GO_4.1 scenario 9.a -> campi non validi
     */
    @Test
    void testDoGet_AddressForm_Error() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(session.getAttribute("righeDisponibili")).thenReturn(new ArrayList<>());

        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("");  // errore
        when(request.getParameter("cap")).thenReturn("abc");     // errore
        when(request.getParameter("citta")).thenReturn("");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso principale: inserimento sede -> pagamentoOrdine.jsp
     */
    @Test
    void testDoGet_SedeForm_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(session.getAttribute("righeDisponibili")).thenReturn(new ArrayList<>());

        when(request.getParameter("typeForm")).thenReturn("sede");
        when(request.getParameter("sede")).thenReturn("1");

        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: sede non specificata -> errore
     */
    @Test
    void testDoGet_SedeForm_Error() throws ServletException, IOException {
        Utente user = new Utente();
        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setDisponibile(true);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setIdCarrello("1");
        righeDisponibili.add(rigaCarrello);

        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("typeForm")).thenReturn("sede");
        when(request.getParameter("sede")).thenReturn(""); // vuoto => errore

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
}