package controller.utente.ordine;

import controller.utente.ordine.OrdineServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.gestoreService.Gestore;
import model.gestoreService.GestoreDAO;
import model.libroService.Libro;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

class OrdineServletTest {

    private OrdineServlet servletUnderTest;
    private RigaCarrelloDAO rigaCarrelloDAO;
    private CarrelloDAO carrelloDAO;
    private OrdineDAO ordineDAO;
    private TesseraDAO tesseraDAO;
    private GestoreDAO gestoreDAO;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new OrdineServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        ordineDAO = mock(OrdineDAO.class);
        carrelloDAO = mock(CarrelloDAO.class);
        rigaCarrelloDAO = mock(RigaCarrelloDAO.class);
        tesseraDAO = mock(TesseraDAO.class);
        gestoreDAO = mock(GestoreDAO.class);

        servletUnderTest.setOrdineDAO(ordineDAO);
        servletUnderTest.setCarrelloDAO(carrelloDAO);
        servletUnderTest.setRigaCarrelloDAO(rigaCarrelloDAO);
        servletUnderTest.setTesseraDAO(tesseraDAO);
        servletUnderTest.setGestoreDAO(gestoreDAO);
        doNothing().when(ordineDAO).doSave(any(Ordine.class));
        when(gestoreDAO.doRetrivedAll()).thenReturn(List.of(new Gestore()));
        when(request.getSession()).thenReturn(session);
    }

    /**
     * Flusso principale: Salvataggio ordine con successo -> redirect index.html
     * UC_GO_4.3 main scenario
     */
    @Test
    void testDoGet_Success() throws ServletException, IOException {
        // Utente standard
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("mario@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        // Parametri
        when(request.getParameter("indirizzo")).thenReturn("Via Roma 1");
        when(request.getParameter("citta")).thenReturn("Napoli");
        when(request.getParameter("punti")).thenReturn("0"); // se standard

        // righeDisponibili
        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setIsbn("1111111111111");
        libro.setPrezzo(10.0);
        libro.setSconto(10);
        libro.setDisponibile(true);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("2");
        rigaCarrello.setLibro(libro);
        righeDisponibili.add(rigaCarrello); // TOT = (10 - 10%)=9 *2=18

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);

        // Carrello in session
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("C0001");
        carrello.setEmail("mario@example.com");
        List<RigaCarrello> righeCarrello = new ArrayList<RigaCarrello>(righeDisponibili);
        carrello.setRigheCarrello(righeCarrello);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente("mario@example.com")).thenReturn(carrello);
        doNothing().when(rigaCarrelloDAO).deleteRigaCarrello(anyString(), anyString());

        // Esecuzione
        servletUnderTest.doGet(request, response);

        // Verifica che la servlet fa un redirect alla home
        verify(response).sendRedirect("index.html");
        verify(dispatcher, never()).forward(request, response);

        // Se avessi iniettato OrdineDAO, potresti verify(ordineDAO).doSave(...)
        // Ma qui, la servlet fa new OrdineDAO() => non direttamente testabile con mocking
    }
}